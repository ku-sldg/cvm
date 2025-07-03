From CVM Require Import Impl Session_Config_Compiler AM_Handler AM_Manager.
From CoplandManifestTools Require Import Manifest.
From CLITools Require Import CLI_Tools.
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

cvm --manifest <manifest>.json --asp_bin <asp_bin_file_location> --req <req>.json
*)

Definition manifest_arg_spec : arg_spec := {|
  arg_name := "manifest";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The manifest file to use for the CVM.";
  arg_default := None
|}.

Definition asp_bin_arg_spec : arg_spec := {|
  arg_name := "asp_bin";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The ASP binary file location.";
  arg_default := None
|}.

(* Definition ipport_arg_spec : arg_spec := {|
  arg_name := "ipport";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The IP:Port to use for the CVM.";
  arg_default := None
|}. *)

Definition request_arg_spec : arg_spec := {|
  arg_name := "req";
  arg_kind := ArgOption;
  arg_required := true;
  arg_help := "The request for the CVM to execute";
  arg_default := None
|}.

Definition unwrap_opt {A B} (opt: option A) (alt : B) : Result A B :=
  match opt with
  | Some v => res v
  | None => err alt
  end.

Local Open Scope map_scope.

Definition cvm_front_end : unit := 
  let comname := CommandLine.name tt in
  let comargs := CommandLine.arguments tt in
  let args_spec := 
    [manifest_arg_spec; asp_bin_arg_spec; request_arg_spec] in
  let runtime := (
    args_res <- gather_args_stub comname comargs args_spec ;;
    (* Parse the args into the values *)
    (* Get the manifest value *)
    manifest_arg <- unwrap_opt (args_res ![ "manifest" ]) "Manifest argument is required." ;;
    manifest_arg <- unwrap_opt (arg_value manifest_arg) "Manifest argument value was not found." ;;
    manifest_val <- from_string manifest_arg ;;
    (* Getting the ASP binary argument *)
    asp_bin_arg <- unwrap_opt (args_res ![ "asp_bin" ]) "ASP binary argument is required." ;;
    asp_bin_arg <- unwrap_opt (arg_value asp_bin_arg) "ASP binary argument value was not found." ;;
    asp_bin_val <- from_string asp_bin_arg ;;
    let am_manager_conf := (mkAM_Man_Conf asp_bin_val manifest_val) in
    (* Getting the request argument *)
    request_arg <- unwrap_opt (args_res ![ "req" ]) "Request argument is required." ;;
    request_arg <- unwrap_opt (arg_value request_arg) "Request argument value was not found." ;;
    (* Actually process the request *)
    resp_str <- handle_AM_request am_manager_conf request_arg ;;
    (* Print the response *)
    res (TextIO.printLn resp_str)
  ) in
  match runtime with
  | res _ => tt
  | err e => TextIO.printLn_err ("Error in CVM Execution: " ++ e)
  end.

Local Close Scope map_scope.
Local Close Scope string_scope.

Separate CakeML_Extraction cvm_front_end.