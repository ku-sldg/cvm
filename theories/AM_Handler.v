From RocqCandy Require Import All.
From RocqJSON Require Import JSON.
From CoplandSpec Require Import System_Types.
From CoplandManifestTools Require Import Manifest.
From CVM Require Import Impl St Interface.Interface Session_Config_Compiler AM_Manager.

(* Processes the request given by [reqstr] and returns a string (json response) value *)
Definition handle_AM_request (conf : AM_Manager_Config) (reqstr : string) 
    : Result string string :=
  jsreq <- from_string reqstr ;;
  action_str <- JSON_get_string STR_ACTION jsreq ;;
  if (dec_eq action_str STR_RUN) then
    (* Run the protocol *)
    '(mkPRReq att_sess req_plc init_ev term) <- from_JSON jsreq ;;
    let sc := session_config_compiler conf att_sess in
    let init_st := mk_st [] 0 in
    let '(cvm_resp, _) := build_cvm init_ev term sc init_st in
    match cvm_resp with
    | err e => err (CVM_Error_to_string e)
    | res ev => res (to_string (to_JSON (mkPRResp true ev)))
    end
  else if (dec_eq action_str STR_NEGOTIATE) then
    err "Negotiate action not implemented yet"
  else if (dec_eq action_str STR_APPSUMM) then
    err "App summary action not implemented yet"
  else err ("Invalid request action: " ++ action_str).