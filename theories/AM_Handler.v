From RocqCandy Require Import All.
From RocqJSON Require Import JSON.
From CoplandSpec Require Import System_Types Interface.Interface.
From CoplandManifestTools Require Import Manifest.
From CVM Require Import Impl St Session_Config_Compiler AM_Manager.
From EasyBakeCakeML Require Import CakeML_Stdlib.All.

Local Open Scope string_scope.

(* Returns true if the term contains a bpar node anywhere in its structure *)
Fixpoint term_has_bpar (t : Term) : bool :=
  match t with
  | asp _           => false
  | att _ t'        => term_has_bpar t'
  | lseq t1 t2      => orb (term_has_bpar t1) (term_has_bpar t2)
  | bseq _ t1 t2    => orb (term_has_bpar t1) (term_has_bpar t2)
  | bpar _ _ _      => true
  end.

(* CVM startup file path written before bpar execution begins.
   The parallel_vm_thread stub reads this to locate the CVM binary and
   session configuration needed to launch a subprocess CVM instance. *)
Definition CVM_STARTUP_FILE : string := "/tmp/cvm_startup.json".

(* Build the startup JSON containing all configuration a subprocess CVM
   needs: the binary path, manifest, ASP binary directory, and att_sess. *)
Definition build_startup_json
    (conf : AM_Manager_Config)
    (att_sess : Attestation_Session)
    (cvm_bin : string) : JSON :=
  JSON_Object [
    ("cvm_binary",  JSON_String cvm_bin);
    ("manifest",    to_JSON (am_manager_manifest conf));
    ("asp_bin",     JSON_String (am_manager_asp_bin conf));
    ("att_sess",    to_JSON att_sess)
  ].

(* Processes the request given by [reqstr] and returns a string (json response) value.
   [cvm_binary_opt] is the path to the CVM binary used to spawn parallel subprocess
   instances when the term contains a bpar node. *)
Definition handle_AM_request
    (conf : AM_Manager_Config)
    (cvm_binary_opt : option string)
    (reqstr : string)
    : Result string string :=
  jsreq <- from_string reqstr ;;
  action_str <- JSON_get_string STR_ACTION jsreq ;;
  if (dec_eq action_str STR_RUN) then
    (* Run the protocol *)
    '(mkPRReq att_sess req_plc init_ev term) <- from_JSON jsreq ;;
    (* Warn if the term contains bpar but no cvm_binary was provided.
       The CVM_Config monad reader carries cvm_binary to start_par_subprocess;
       no startup file is written (Option B). *)
    let _ :=
      if term_has_bpar term then
        match cvm_binary_opt with
        | Some _ => tt
        | None =>
          TextIO.printLn_err
            "WARNING: term contains bpar but --cvm_binary was not provided; \
             parallel branches will return an error."
        end
      else tt
    in
    let sc  := session_config_compiler conf att_sess in
    let cfg := mk_cvm_cfg sc
                 (am_manager_asp_bin conf)
                 (match cvm_binary_opt with Some b => b | None => "" end)
                 (am_manager_manifest conf) in
    let init_st := mk_st [] 0 in
    let '(cvm_resp, _) := build_cvm init_ev term cfg init_st in
    match cvm_resp with
    | err e => err (CVM_Error_to_string e)
    | res ev => res (to_string (to_JSON (mkPRResp true ev)))
    end
  else if (dec_eq action_str STR_NEGOTIATE) then
    err "Negotiate action not implemented yet"
  else if (dec_eq action_str STR_APPSUMM) then
    err "App summary action not implemented yet"
  else err ("Invalid request action: " ++ action_str).

Local Close Scope string_scope.