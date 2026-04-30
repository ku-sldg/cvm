From CVM Require Import Impl Session_Config_Compiler AM_Handler AM_Manager.
From CoplandManifestTools Require Import Manifest.
From CLITools Require Import CLI_Tools.
From RocqLogging Require Import Logging.
From RocqJSON Require Import JSON.
From EasyBakeCakeML Require Import
  EasyBakeCakeML
  ExtrCakeMLNativeString
  ExtrCakeMLNat
  CakeML_Stdlib.All.
From RocqCandy Require Import All.

(*
Inductive cli_arg_kind :=
  | ArgPositional
  | ArgOption
  | ArgFlag.

Record arg_spec := {
  arg_name : string;
  arg_kind : cli_arg_kind;
  arg_required : bool;
  arg_help : string;
  arg_default : option string
}.
*)

Local Open Scope string_scope.

(*
Here is the usage we are aiming for:

cvm [--manifest <manifest_json_value> | --manifest_file <manifest_file_path>.json] --asp_bin <asp_bin_file_location> [--req <req_json_value> | --req_file <req_file_path>.json]

Where the manifest can be provided either as a JSON string or as a file path, and the request can also be provided either as a JSON string or as a file path.
*)

Definition manifest_arg_spec : arg_spec := {|
  arg_name := "manifest";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The JSON value of the manifest to use for the CVM.";
  arg_default := None
|}.

Definition manifest_file_arg_spec : arg_spec := {|
  arg_name := "manifest_file";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The file path to the manifest JSON file to use for the CVM.";
  arg_default := None
|}.

Definition asp_bin_arg_spec : arg_spec := {|
  arg_name := "asp_bin";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The ASP binary file location.";
  arg_default := None
|}.

Definition request_arg_spec : arg_spec := {|
  arg_name := "req";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The JSON value of the request for the CVM to execute";
  arg_default := None
|}.

Definition request_file_arg_spec : arg_spec := {|
  arg_name := "req_file";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The file path to the request JSON file to use for the CVM.";
  arg_default := None
|}.

Definition cvm_binary_arg_spec : arg_spec := {|
  arg_name := "cvm_binary";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "Path to this CVM binary, used to spawn subprocess CVM instances for parallel (bpar) terms.";
  arg_default := None
|}.

(*
Inductive LogLevel : Type :=
| Debug
| Info
| Warning
| Error
| Critical.
*)
Local Instance Stringifiable_LogLevel : Stringifiable LogLevel := {
  to_string l := 
    match l with
    | Debug => "Debug"
    | Info => "Info"
    | Warning => "Warning"
    | Error => "Error"
    | Critical => "Critical"
    end;
  from_string s :=
    match s with
    | "Debug" => res Debug
    | "Info" => res Info
    | "Warning" => res Warning
    | "Error" => res Error
    | "Critical" => res Critical
    | _ => err ("Invalid LogLevel string: '" ++ s ++ "', valid values are [ 'Debug', 'Info', 'Warning', 'Error', 'Critical' ].")
    end;
  canonical_stringification s := 
      match s with 
      | Debug => eq_refl
      | Info => eq_refl
      | Warning => eq_refl
      | Error => eq_refl
      | Critical => eq_refl
      end
}.

Definition log_level_arg_spec : arg_spec := {|
  arg_name := "log_level";
  arg_kind := ArgOption;
  arg_required := false;
  arg_help := "The logging level to use.";
  arg_default := Some ("Debug")
|}.

Definition unwrap_opt {A B} (opt: option A) (alt : B) : Result A B :=
  match opt with
  | Some v => res v
  | None => err alt
  end.

(* Shim for reading all of stdin.  CakeML's TextIO.stdIn is not modeled
   in EasyBakeCakeML, so we introduce it here as an inlined extraction
   constant and build read_all_stdin from it. *)
Definition stdin_stream : TextIO.instream. Admitted.
Extract Inlined Constant stdin_stream => "TextIO.stdIn".

Definition read_all_stdin : string := TextIO.inputAll stdin_stream.

Local Open Scope map_scope.

Definition cvm_front_end : unit :=
  let comname := CommandLine.name tt in
  let comargs := CommandLine.arguments tt in
  (* ------------------------------------------------------------------ *
   * Stdin mode: when the process is invoked with no CLI arguments (e.g.
   * as a subprocess CVM for a bpar branch), the full ProtocolRunRequest
   * JSON blob is read from stdin.  The manifest, asp_bin, and
   * cvm_binary fields are embedded directly in that JSON blob (written
   * by the parent CVM's handle_AM_request via the startup file, and
   * reconstructed by parallel_vm_thread before exec).
   * ------------------------------------------------------------------ *)
  match comargs with
  | [] =>
    (* Stdin mode: the subprocess CVM receives a single inline bundle JSON
       on stdin, containing all config it needs plus the ProtocolRunRequest.
       Format: { "cvm_binary": "...", "manifest": {...}, "asp_bin": "...",
                 "request": { <PRReq JSON object> } }
       No startup file is read; everything comes from the bundle. *)
    let bundle_str := read_all_stdin in
    let runtime : Result string string := (
      bundle_js    <- from_string bundle_str ;;
      manifest_js  <- JSON_get_Object "manifest"   bundle_js ;;
      asp_bin_val  <- JSON_get_string "asp_bin"    bundle_js ;;
      cvm_bin_str  <- JSON_get_string "cvm_binary" bundle_js ;;
      req_js       <- JSON_get_Object "request"    bundle_js ;;
      manifest_val <- from_JSON manifest_js ;;
      let am_manager_conf := mkAM_Man_Conf manifest_val asp_bin_val in
      let cvm_binary_opt  := Some cvm_bin_str in
      let req_str         := to_string req_js in
      handle_AM_request am_manager_conf cvm_binary_opt req_str
    ) in
    match runtime with
    | res resp_str => TextIO.printLn resp_str
    | err e => TextIO.printLn_err ("Error in CVM Execution (stdin mode): " ++ e)
    end
  | _ =>
  (* Normal CLI mode *)
  let args_spec :=
    [log_level_arg_spec; manifest_arg_spec; manifest_file_arg_spec;
     asp_bin_arg_spec; request_arg_spec; request_file_arg_spec;
     cvm_binary_arg_spec] in
  let runtime := (
    args_res <- gather_args_stub comname comargs args_spec ;;
    (* let _ := log Debug Debug (to_string args_res) in *)
    (* First get the logging level *)
    log_level_arg <- unwrap_opt (args_res ![ "log_level" ]) "Log level argument is required." ;;
    log_level_val <- unwrap_opt (arg_value log_level_arg) "Log level argument value was not found." ;;
    log_level <- from_string log_level_val ;;
    let debug_log msg := (res (log log_level Debug msg)) in
    (* Parse the args into the values *)
    (* Get the manifest value *)
    _ <- debug_log "Parsing manifest arguments." ;;
    (* Getting the manifest argument *)
    manifest_arg <- unwrap_opt (args_res ![ "manifest" ]) "Manifest argument is required." ;;
    manifest_file_arg <- unwrap_opt (args_res ![ "manifest_file" ]) "Manifest file argument is required." ;;
    manifest_val <-
      match arg_found manifest_arg, arg_found manifest_file_arg with
      | true, true => err "Both manifest and manifest_file arguments were provided. Please provide only one."
      | true, false =>
        arg_val <- unwrap_opt (arg_value manifest_arg) "Manifest argument value was not found." ;;
        from_string arg_val
      | false, true =>
        arg_val <- unwrap_opt (arg_value manifest_file_arg) "Manifest file argument value was not found." ;;
        (* Read the file content if manifest_file is provided *)
        (* NOTE: This should probably be exception catching, but not done yet! *)
        let str_val := TextIO.readFile arg_val in
        from_string str_val
      | false, false => err "Manifest argument is required. Please provide either --manifest or --manifest_file."
      end ;;
    _ <- debug_log ("Manifest value: " ++ (to_string manifest_val)) ;;
    (* Getting the ASP binary argument *)
    _ <- debug_log "Parsing ASP binary argument." ;;
    (* Getting the ASP binary argument *)
    asp_bin_arg <- unwrap_opt (args_res ![ "asp_bin" ]) "ASP binary argument is required." ;;
    asp_bin_val <- unwrap_opt (arg_value asp_bin_arg) "ASP binary argument value was not found." ;;
    _ <- debug_log ("ASP binary value: " ++ asp_bin_val) ;;
    (* Parse the manifest *)
    let am_manager_conf := (mkAM_Man_Conf manifest_val asp_bin_val) in
    (* Extract the optional cvm_binary argument *)
    let cvm_binary_opt :=
      match args_res ![ "cvm_binary" ] with
      | Some arg => arg_value arg
      | None => None
      end
    in
    (* Getting the request argument *)
    _ <- debug_log "Parsing request arguments." ;;
    request_arg <- unwrap_opt (args_res ![ "req" ]) "Request argument is required." ;;
    request_file_arg <- unwrap_opt (args_res ![ "req_file" ]) "Request file argument is required." ;;
    request_str <-
      match arg_found request_arg, arg_found request_file_arg with
      | true, true => err "Both req and req_file arguments were provided. Please provide only one."
      | true, false =>
        _ <- debug_log "Using request argument value." ;;
        (* If req is provided, use it directly *)
        arg_val <- unwrap_opt (arg_value request_arg) "Request argument value was not found." ;;
        _ <- debug_log ("Request argument value: " ++ arg_val) ;;
        res arg_val
      | false, true =>
        _ <- debug_log "Using request file argument value." ;;
        (* If req_file is provided, read the file content *)
        arg_val <- unwrap_opt (arg_value request_file_arg) "Request file argument value was not found." ;;
        _ <- debug_log ("Request file argument value: " ++ arg_val) ;;
        (* NOTE: This should probably be exception catching, but not done yet! *)
        let str_val := TextIO.readFile arg_val in
        _ <- debug_log ("Request file content: " ++ str_val) ;;
        res str_val
      | false, false => err "Request argument is required. Please provide either --req or --req_file."
      end ;;
    (* Actually process the request *)
    handle_AM_request am_manager_conf cvm_binary_opt request_str
  ) in
  match runtime with
  | res resp_str => TextIO.printLn resp_str
  | err e => TextIO.printLn_err ("Error in CVM Execution: " ++ e)
  end
  end.

Local Close Scope map_scope.
Local Close Scope string_scope.

Separate CakeML_Extraction cvm_front_end.