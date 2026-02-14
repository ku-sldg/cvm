#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/wait.h>
#include "shared_ffi_fns.h"
#include "buffer_manager.h"

#define SUCCESS 0x00
#define BUFFER_OVERFLOW 0xe0
#define PATH_ERROR 0xe1
#define FORK_ERROR 0xe2
#define PIPE_ERROR 0xe3

#define STDIN_WRITE_ERROR 0xe5
#define FAILED_TO_READ_FILE 0xed
#define FAILED_TO_REALLOC_BUFFER 0xee
#define FAILED_TO_ALLOCATE_BUFFER 0xef
#define INSUFFICIENT_OUTPUT 0xf0
#define NEED_MORE_THAN_32_BITS_FOR_LENGTH 0xf1
#define INPUT_DECODE_ERROR 0xf2
#define FILE_READ_ERROR 0xfe
#define FILE_CLOSE_ERROR 0xff

/**
 * Function to read from a FILE* stream until EOF via buffered I/O.
 * Returns:
 *
 * 0x00 = Success
 * 0xe0 = Buffer overflow (should not happen with proper sizing)
 * 0xed = Failed to read from file properly
 * 0xee = Buffer reallocation error
 * 0xef = Failed to allocate initial buffer
 *
 * Note: On error, *buffer is set to NULL and any allocated memory is freed.
 */
uint8_t read_until_eof(FILE *file, size_t INITIAL_BUFFER_SIZE, char **buffer, size_t *total_read)
{
  // Input validation
  if (file == NULL || buffer == NULL || total_read == NULL)
  {
    DEBUG_PRINTF("read_until_eof: Invalid input parameters\n");
    if (buffer != NULL)
      *buffer = NULL;
    if (total_read != NULL)
      *total_read = 0;
    return FAILED_TO_ALLOCATE_BUFFER;
  }

  // Ensure minimum buffer size
  if (INITIAL_BUFFER_SIZE < 64)
  {
    INITIAL_BUFFER_SIZE = 64;
  }

  size_t buffer_size = INITIAL_BUFFER_SIZE;
  *total_read = 0;
  *buffer = malloc(buffer_size);

  if (*buffer == NULL)
  {
    DEBUG_PRINTF("read_until_eof: Failed to allocate initial buffer of size %zu\n", buffer_size);
    return FAILED_TO_ALLOCATE_BUFFER;
  }

  size_t bytes_read;
  while ((bytes_read = fread(
              *buffer + *total_read,         // Start writing at the start of the buffer + any offset for what we've already read
              1,                             // Read 1 byte at a time
              buffer_size - *total_read - 1, // Read all the way to the end of the buffer - the items already read - 1 for null terminator
              file)) > 0)
  {
    *total_read += bytes_read;

    // Check if we need to resize the buffer
    if (*total_read + 1 > buffer_size)
    {
      // This should never happen, but just in case
      DEBUG_PRINTF("read_until_eof: Buffer overflow detected\n");
      free(*buffer);
      *buffer = NULL;
      return BUFFER_OVERFLOW;
    }
    else if (*total_read >= (buffer_size - 1))
    {
      buffer_size *= 2;
      DEBUG_PRINTF("read_until_eof: Resizing buffer from %zu to %zu bytes\n", buffer_size / 2, buffer_size);
      // Resize and reallocate (safely moves the ptrs)
      char *new_buffer = realloc(*buffer, buffer_size);

      // Checks if realloc fails
      if (new_buffer == NULL)
      {
        DEBUG_PRINTF("read_until_eof: Failed to reallocate buffer to %zu bytes\n", buffer_size);
        // Ptr wasn't properly moved, so we need to free the old buffer
        free(*buffer);
        *buffer = NULL;
        return FAILED_TO_REALLOC_BUFFER;
      }

      // Update the buffer ptr, (realloc already freed the old buffer)
      *buffer = new_buffer;
    }
  }

  // Handle errors in fread
  if (ferror(file))
  {
    DEBUG_PRINTF("read_until_eof: Error reading from file\n");
    free(*buffer);
    *buffer = NULL;
    return FAILED_TO_READ_FILE;
  }

  // Null-terminate the buffer
  (*buffer)[*total_read] = '\0';

  return SUCCESS;
}

/**
 * Write all bytes to a file descriptor, handling partial writes.
 * Returns 0 on success, -1 on failure.
 */
static int write_all(int fd, const char *data, size_t len)
{
  size_t total_written = 0;
  while (total_written < len)
  {
    ssize_t n = write(fd, data + total_written, len - total_written);
    if (n < 0)
    {
      if (errno == EINTR)
        continue; // Retry on interrupt
      DEBUG_PRINTF("write_all: write() failed: %s\n", strerror(errno));
      return -1;
    }
    total_written += (size_t)n;
  }
  return 0;
}

/**
 * Close a file descriptor and log any errors (best-effort).
 */
static void safe_close(int fd)
{
  if (fd >= 0 && close(fd) != 0)
  {
    DEBUG_PRINTF("safe_close: close(%d) failed: %s\n", fd, strerror(errno));
  }
}

/**
 * FFI function to spawn a process, send input on its stdin, close the write
 * end of the pipe (allowing the process to finish reading), and then read
 * the process's stdout output.
 *
 * Input encoding (in commandIn, total length clen):
 * [  ProcessPathLength : 4 Bytes (big-endian) ;
 *    ProcessPath       : ProcessPathLength Bytes ;
 *    ArgString         : remaining bytes (clen - 4 - ProcessPathLength)
 * ]
 *
 * Output format in buffer 'a':
 * [  Success_Code  : 1 Byte ;
 *    OutputLength  : 4 Bytes (big-endian) ;
 *    OutputBuffId  : 4 Bytes (big-endian) ;
 * ]
 *
 * Return codes:
 * 0x00 = Success
 * 0xe1 = Invalid path (must be absolute, no '..' allowed)
 * 0xe2 = Fork failed
 * 0xe3 = Pipe creation failed
 * 0xe4 = Exec failed (child could not execute process)
 * 0xe5 = Failed to write input to child stdin
 * 0xf1 = Output too large (>UINT32_MAX bytes)
 * 0xf2 = Input decoding error (malformed input buffer)
 * 0xfe = General I/O / read error
 * 0xff = Command execution failed (non-zero exit)
 * 0xed-0xef = Buffer allocation/read errors
 */
void ffiexec_process_io(const char *commandIn, const long clen, char *a, const long alen)
{
  const uint8_t RESPONSE_CODE_START = 0;
  const uint8_t RESPONSE_CODE_LENGTH = 1;
  const uint8_t OUTPUT_LENGTH_START = RESPONSE_CODE_START + RESPONSE_CODE_LENGTH;
  const uint8_t OUTPUT_LENGTH_LENGTH = 4;
  const uint8_t OUTPUT_BUFFER_ID_START = OUTPUT_LENGTH_START + OUTPUT_LENGTH_LENGTH;
  const uint8_t OUTPUT_BUFFER_ID_LENGTH = 4;
  const uint8_t HEADER_LENGTH = OUTPUT_BUFFER_ID_START + OUTPUT_BUFFER_ID_LENGTH;

  const uint8_t INPUT_PATH_LEN_SIZE = 4; // 4 bytes for process path length

  // ---------- Input validation ----------
  if (commandIn == NULL || a == NULL || alen < HEADER_LENGTH || clen <= 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Invalid input parameters\n");
    DEBUG_PRINTF("ffiexec_process_io: commandIn: %p, clen: %ld, a: %p, alen: %ld\n",
                 (const void *)commandIn, clen, (void *)a, alen);
    if (a != NULL && alen >= 1)
    {
      a[RESPONSE_CODE_START] = FILE_READ_ERROR;
    }
    return;
  }

  // Zero-initialize the output header
  memset(a, 0, (size_t)alen);

  // ---------- Decode input: extract process path and arg string ----------
  if ((size_t)clen < INPUT_PATH_LEN_SIZE)
  {
    DEBUG_PRINTF("ffiexec_process_io: Input too short to contain path length header\n");
    a[RESPONSE_CODE_START] = INPUT_DECODE_ERROR;
    return;
  }

  // Read process path length (big-endian, 4 bytes)
  int process_path_len = qword_to_int((unsigned char *)commandIn);
  if (process_path_len <= 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Invalid process path length: %d\n", process_path_len);
    a[RESPONSE_CODE_START] = INPUT_DECODE_ERROR;
    return;
  }

  size_t path_end = (size_t)INPUT_PATH_LEN_SIZE + (size_t)process_path_len;
  if (path_end > (size_t)clen)
  {
    DEBUG_PRINTF("ffiexec_process_io: Process path length (%d) exceeds input buffer (clen=%ld)\n",
                 process_path_len, clen);
    a[RESPONSE_CODE_START] = INPUT_DECODE_ERROR;
    return;
  }

  // Extract a null-terminated copy of the process path
  char *process_path = malloc((size_t)process_path_len + 1);
  if (process_path == NULL)
  {
    DEBUG_PRINTF("ffiexec_process_io: Failed to allocate process path buffer\n");
    a[RESPONSE_CODE_START] = FAILED_TO_ALLOCATE_BUFFER;
    return;
  }
  memcpy(process_path, commandIn + INPUT_PATH_LEN_SIZE, (size_t)process_path_len);
  process_path[process_path_len] = '\0';

  // The remaining bytes are the argument / stdin input string
  const char *arg_str = commandIn + path_end;
  size_t arg_str_len = (size_t)clen - path_end;

  DEBUG_PRINTF("ffiexec_process_io: Process path: %s\n", process_path);
  DEBUG_PRINTF("ffiexec_process_io: Arg string length: %zu\n", arg_str_len);

  // ---------- Validate process path ----------
  if (process_path[0] != '/' || strstr(process_path, "..") != NULL)
  {
    DEBUG_PRINTF("ffiexec_process_io: Invalid path (must be absolute, no '..'): %s\n", process_path);
    free(process_path);
    a[RESPONSE_CODE_START] = PATH_ERROR;
    return;
  }

  // ---------- Create pipes ----------
  int stdin_pipe[2];  // Parent writes to [1], child reads from [0]
  int stdout_pipe[2]; // Child writes to [1], parent reads from [0]

  if (pipe(stdin_pipe) != 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Failed to create stdin pipe: %s\n", strerror(errno));
    free(process_path);
    a[RESPONSE_CODE_START] = PIPE_ERROR;
    return;
  }

  if (pipe(stdout_pipe) != 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Failed to create stdout pipe: %s\n", strerror(errno));
    safe_close(stdin_pipe[0]);
    safe_close(stdin_pipe[1]);
    free(process_path);
    a[RESPONSE_CODE_START] = PIPE_ERROR;
    return;
  }

  // ---------- Fork ----------
  pid_t pid = fork();
  if (pid < 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: fork() failed: %s\n", strerror(errno));
    safe_close(stdin_pipe[0]);
    safe_close(stdin_pipe[1]);
    safe_close(stdout_pipe[0]);
    safe_close(stdout_pipe[1]);
    free(process_path);
    a[RESPONSE_CODE_START] = FORK_ERROR;
    return;
  }

  if (pid == 0)
  {
    // ===== CHILD PROCESS =====
    // Redirect stdin to read end of stdin_pipe
    close(stdin_pipe[1]); // Close write end (parent uses this)
    if (dup2(stdin_pipe[0], STDIN_FILENO) < 0)
    {
      _exit(127);
    }
    close(stdin_pipe[0]);

    // Redirect stdout to write end of stdout_pipe
    close(stdout_pipe[0]); // Close read end (parent uses this)
    if (dup2(stdout_pipe[1], STDOUT_FILENO) < 0)
    {
      _exit(127);
    }
    close(stdout_pipe[1]);

    // Execute the process (no shell involved — direct exec)
    execl(process_path, process_path, (char *)NULL);

    // If execl returns, it failed.
    // Note: The error message is written to the child's stderr, which is not
    // redirected or captured and therefore will appear on the parent's stderr.
    fprintf(stderr, "ffiexec_process_io: execl failed for '%s': %s\n",
            process_path, strerror(errno));
    _exit(127);
  }

  // ===== PARENT PROCESS =====
  // Close pipe ends we don't use
  safe_close(stdin_pipe[0]);  // We don't read from child's stdin
  safe_close(stdout_pipe[1]); // We don't write to child's stdout

  // We no longer need the path string
  free(process_path);
  process_path = NULL;

  // ---------- Write arg_str to child's stdin, then close ----------
  if (arg_str_len > 0)
  {
    if (write_all(stdin_pipe[1], arg_str, arg_str_len) != 0)
    {
      DEBUG_PRINTF("ffiexec_process_io: Failed to write input to child stdin\n");
      safe_close(stdin_pipe[1]);
      safe_close(stdout_pipe[0]);
      // Attempt to reap the child to avoid zombie
      waitpid(pid, NULL, 0);
      a[RESPONSE_CODE_START] = STDIN_WRITE_ERROR;
      return;
    }
  }

  // Close write end → sends EOF to the child's stdin
  safe_close(stdin_pipe[1]);

  // ---------- Read child's stdout ----------
  FILE *child_stdout = fdopen(stdout_pipe[0], "r");
  if (child_stdout == NULL)
  {
    DEBUG_PRINTF("ffiexec_process_io: fdopen failed on child stdout: %s\n", strerror(errno));
    safe_close(stdout_pipe[0]);
    waitpid(pid, NULL, 0);
    a[RESPONSE_CODE_START] = FILE_READ_ERROR;
    return;
  }

  char *buffer = NULL;
  size_t output_length = 0;
  uint8_t out_code = read_until_eof(child_stdout, 4096, &buffer, &output_length);
  DEBUG_PRINTF("ffiexec_process_io: Read %zu bytes from child stdout\n", output_length);

  // fclose also closes the underlying fd (stdout_pipe[0])
  fclose(child_stdout);

  // ---------- Wait for child to exit ----------
  int status = 0;
  pid_t wp;
  do
  {
    wp = waitpid(pid, &status, 0);
  } while (wp < 0 && errno == EINTR);

  if (wp < 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: waitpid failed: %s\n", strerror(errno));
    if (buffer != NULL)
      free(buffer);
    a[RESPONSE_CODE_START] = FILE_READ_ERROR;
    return;
  }

  // Check child exit status
  if (WIFEXITED(status) && WEXITSTATUS(status) != 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Child exited with code %d\n", WEXITSTATUS(status));
    if (buffer != NULL)
      free(buffer);
    a[RESPONSE_CODE_START] = FILE_CLOSE_ERROR;
    return;
  }
  else if (WIFSIGNALED(status))
  {
    DEBUG_PRINTF("ffiexec_process_io: Child killed by signal %d\n", WTERMSIG(status));
    if (buffer != NULL)
      free(buffer);
    a[RESPONSE_CODE_START] = FILE_CLOSE_ERROR;
    return;
  }

  // ---------- Handle read errors ----------
  if (out_code != SUCCESS)
  {
    DEBUG_PRINTF("ffiexec_process_io: Error reading child output: %d\n", out_code);
    if (buffer != NULL)
      free(buffer);
    a[RESPONSE_CODE_START] = out_code;
    return;
  }

  if (buffer == NULL)
  {
    DEBUG_PRINTF("ffiexec_process_io: No buffer allocated despite SUCCESS status\n");
    a[RESPONSE_CODE_START] = FAILED_TO_ALLOCATE_BUFFER;
    return;
  }

  // ---------- Validate output length ----------
  if (output_length > UINT32_MAX)
  {
    DEBUG_PRINTF("ffiexec_process_io: Output length %zu exceeds UINT32_MAX\n", output_length);
    free(buffer);
    a[RESPONSE_CODE_START] = NEED_MORE_THAN_32_BITS_FOR_LENGTH;
    return;
  }

  // ---------- Store output in buffer manager and write response header ----------
  int buffer_id = set_new_buffer((long)output_length, buffer);
  if (buffer_id < 0)
  {
    DEBUG_PRINTF("ffiexec_process_io: Failed to store output buffer (error %d)\n", buffer_id);
    free(buffer);
    a[RESPONSE_CODE_START] = FAILED_TO_ALLOCATE_BUFFER;
    return;
  }

  DEBUG_PRINTF("ffiexec_process_io: Stored %zu bytes in buffer %d\n", output_length, buffer_id);

  assert(sizeof(uint32_t) == OUTPUT_LENGTH_LENGTH);
  assert(sizeof(uint32_t) == OUTPUT_BUFFER_ID_LENGTH);
  int_to_qword((int)output_length, (unsigned char *)&a[OUTPUT_LENGTH_START]);
  int_to_qword(buffer_id, (unsigned char *)&a[OUTPUT_BUFFER_ID_START]);

  a[RESPONSE_CODE_START] = SUCCESS;
  DEBUG_PRINTF("ffiexec_process_io: Function completed successfully\n");
}