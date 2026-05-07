## Summary

This PR implements true parallel execution of `bpar` Copland terms via forked CVM subprocess instances, then eliminates a race condition in how those subprocesses receive their configuration.

**Phase 1 – Sequential subprocess baseline** (commits `4f03dac`–`2127e6a`): introduced subprocess CVM infrastructure. A `parallel_vm_thread` stub forks the CVM binary and communicates via a shared `/tmp/cvm_startup.json` startup file plus a per-request stdin payload.

**Phase 2 – True parallel execution** (commits `3904dfa`–`8546676`): split the sequential stub into non-blocking `start_par_subprocess` + `collect_par_subprocess` primitives backed by new `ffispawn_par_process` / `fficollect_par_process` C FFI functions. The parent CVM launches the subprocess and immediately continues executing `t1` of `bpar`, then blocks only at `collect` time. PID-namespaced handle files (`/tmp/cvm_par_<pid>_<loc>.handle`) prevent nested `bpar` subprocesses from colliding.

**Option B – Inline bundle / eliminate startup file** (commits `f60dced`–`ef933c8`): replaced the shared `/tmp/cvm_startup.json` with an inline bundle JSON sent atomically on subprocess stdin. No file race condition possible between concurrent protocols with different manifests.

---

## Detailed changes

### `theories/St.v`
- Introduced `CVM_Config` record wrapping `Session_Config` with `cc_asp_bin`, `cc_cvm_bin`, and `cc_manifest`
- Changed `CVM A` monad type from `Config Session_Config ...` to `Config CVM_Config ...`
- Added `CVM_ask : CVM CVM_Config` and `CVM_ask_session : CVM Session_Config` (backward-compat projection)

### `theories/Monad.v`
- `get_config` now uses `CVM_ask_session` (all existing call-sites unchanged)
- Added `get_cvm_config : CVM CVM_Config := CVM_ask`
- `start_par_thread` passes `p` to `do_start_par_thread`
- `do_wait_par_thread` switched from `parallel_vm_thread` to `collect_par_subprocess`

### `theories/IO_Axioms.v`
- Added `start_par_subprocess : CVM unit` and `collect_par_subprocess : Result Evidence CVM_Error` (Phase 2 split primitives)

### `theories/IO_Utils.v`
- `do_start_par_thread` wires the `p` argument through to `start_par_subprocess`

### `theories/Cvm_Axioms.v`
- `parallel_vm_thread_axiom` repointed to `collect_par_subprocess` and updated for `CVM_Config`
- Added `start_par_subprocess_axiom : forall i p e t, start_par_subprocess i p e t = CVM_ret tt`
- `do_remote_res_axiom` restructured to existentially witness `cfg' : CVM_Config` with matching `session_context`

### `theories/AM_Handler.v`
- Added `term_has_bpar`, `build_startup_json`, `CVM_STARTUP_FILE` helpers
- `handle_AM_request` gains a `cvm_binary_opt` parameter; builds `CVM_Config` and passes it as the monad reader to `build_cvm`
- Startup file write removed (Option B); warning retained for missing `--cvm_binary` with `bpar` terms

### `theories/FrontEnd.v`
- Added `--cvm_binary` CLI argument
- Added stdin mode (no-arg invocation): reads a single inline bundle JSON `{cvm_binary, manifest, asp_bin, request}` from stdin and dispatches to `handle_AM_request` — no startup file read
- CLI mode: request value no longer pre-parsed to JSON; passed as raw string to `handle_AM_request`

### `theories/Verification.v`
- Updated throughout for `CVM_Config`: `session_plc sc` → `session_plc (cc_session sc)`, etc.
- `cvm_preserves_wf_Evidence` att case updated to use the new `do_remote_res_axiom` existential form

### `stubs/FFI/sys_ffi.c`
- `ffispawn_par_process`: non-blocking fork/exec; writes stdin, closes it, returns `(stdout_read_fd, child_pid)` immediately without waiting
- `fficollect_par_process`: blocks on read/waitpid, returns child stdout via buffer-manager protocol
- `ffic_getpid`: returns calling process PID for handle-file namespacing

### `stubs/FFI/SysFFI.cml`
- `c_spawn_par_process`: CML wrapper for `ffispawn_par_process`, returns `(fd, pid)` pair
- `c_collect_par_process`: CML wrapper for `fficollect_par_process`
- `c_getpid`: CML wrapper for `ffic_getpid`

### `stubs/IO_Axioms.cml`
- `parallel_vm_thread`: kept for reference; still reads startup file (Phase 1 legacy, no longer called from Rocq)
- `start_par_subprocess`: rewritten as 6-arg CVM monad function; extracts config from monad `cfg` arg, reconstructs `att_sess` via `session_config_decompiler`, builds inline bundle JSON `{cvm_binary, manifest, asp_bin, request}`, calls `c_spawn_par_process`
- `collect_par_subprocess`: reads PID-namespaced handle file, calls `c_collect_par_process`, deserializes response
- `par_write_handle` / `par_read_handle`: handle file I/O helpers

---

## Test plan
- [ ] `dune build` passes with no errors (only expected extraction warnings)
- [ ] Verification.v proofs all pass (no new `Admitted`)
- [ ] Single-branch `bpar` attestation produces correct evidence
- [ ] Nested `bpar` (subprocess spawning its own subprocess) does not collide on handle files
- [ ] Concurrent protocols with different manifests do not race on config delivery

🤖 Generated with [Claude Code](https://claude.com/claude-code)
