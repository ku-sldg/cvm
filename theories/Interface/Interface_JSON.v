From RocqCandy Require Import All.
From CVM.Interface Require Import Interface_Types Interface_String_Vars.
From RocqJSON Require Import JSON.
From CoplandSpec Require Import Term_Defs Attestation_Session.

(* Protocol Run Request *)
Global Instance Jsonifiable_ProtocolRunRequest `{Jsonifiable Term,
  Jsonifiable Evidence, Jsonifiable Attestation_Session}: Jsonifiable ProtocolRunRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_ATTEST_SESS, (to_JSON (prreq_att_sess req)));
    (STR_REQ_PLC, (JSON_String (to_string (prreq_req_plc req))));
    (STR_EVIDENCE, (to_JSON (prreq_Evidence req)));
    (STR_TERM, (to_JSON (prreq_term req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_req_plc <- JSON_get_string STR_REQ_PLC j ;;
  temp_ev <- JSON_get_Object STR_EVIDENCE j ;;
  temp_term <- JSON_get_Object STR_TERM j ;;

  att_sess <- from_JSON temp_att_sess ;;
  req_plc <- from_string temp_req_plc ;;
  ev <- from_JSON temp_ev ;;
  term <- from_JSON temp_term ;;
  res (mkPRReq att_sess req_plc ev term)));
solve_json.
Defined.

(* Protocol Run Response *)
Global Instance Jsonifiable_ProtocolRunResponse `{Jsonifiable Evidence}: Jsonifiable ProtocolRunResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_SUCCESS, (JSON_Boolean (prresp_success resp)));
    (STR_PAYLOAD, (to_JSON (prresp_Evidence resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_ev <- JSON_get_Object STR_PAYLOAD resp ;;

  ev <- from_JSON temp_ev ;;
  res (mkPRResp temp_success ev))); solve_json.
Defined.

(* Protocol Negotiate Request *)
Global Instance Jsonifiable_ProtocolNegotiateRequest `{Jsonifiable Term}: Jsonifiable ProtocolNegotiateRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
    (STR_TERM, (to_JSON (pnreq_term req)))])
(from_JSON := (fun j =>
  temp_term <- JSON_get_Object STR_TERM j ;;

  term <- from_JSON temp_term ;;
  res (mkPNReq term))); solve_json.
Defined.

(* Protocol Negotiate Response *)
Global Instance Jsonifiable_ProtocolNegotiateResponse `{Jsonifiable Term}: Jsonifiable ProtocolNegotiateResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
    (STR_SUCCESS, (JSON_Boolean (pnresp_success resp)));
    (STR_PAYLOAD, (to_JSON (pnresp_term resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_term <- JSON_get_Object STR_PAYLOAD resp ;;

  term <- from_JSON temp_term ;;
  res (mkPNResp temp_success term))); solve_json.
Defined.

(* ASP Run Request *)
Global Instance Jsonifiable_ASPRunRequest `{Jsonifiable RawEv, Jsonifiable ASP_ARGS}: Jsonifiable ASPRunRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object [
    (STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_ASP_ID, (JSON_String (to_string (asprreq_asp_id req))));
    (STR_ASP_ARGS, (to_JSON (asprreq_asp_args req)));
    (STR_ASP_PLC, (JSON_String (to_string (asprreq_targ_plc req))));
    (STR_ASP_TARG_ID, (JSON_String (to_string (asprreq_targ req))));
    (STR_RAWEV, (to_JSON (asprreq_rawev req)))])
(from_JSON := (fun j =>
  temp_asp_id <- JSON_get_string STR_ASP_ID j ;;
  temp_asp_args <- JSON_get_Object STR_ASP_ARGS j ;;
  temp_targ_plc <- JSON_get_string STR_ASP_PLC j ;;
  temp_targ <- JSON_get_string STR_ASP_TARG_ID j ;;
  temp_ev <- JSON_get_Object STR_RAWEV j ;;

  asp_id <- from_string temp_asp_id ;;
  asp_args <- from_JSON temp_asp_args ;;
  targ_plc <- from_string temp_targ_plc ;;
  targ <- from_string temp_targ ;;
  ev <- from_JSON temp_ev ;;
  res (mkASPRReq asp_id asp_args targ_plc targ ev))); solve_json.
Defined.

(* ASP Run Response *)
Global Instance Jsonifiable_ASPRunResponse `{Jsonifiable RawEv}: Jsonifiable ASPRunResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_SUCCESS, (JSON_Boolean (asprresp_success resp)));
    (STR_PAYLOAD, (to_JSON (asprresp_rawev resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_rawev <- JSON_get_Object STR_PAYLOAD resp ;;

  rawev <- from_JSON temp_rawev ;;
  res (mkASPRResp temp_success rawev))); solve_json.
Defined.

(* Error Response *)
Definition ErrorResponseJSON (msg: string): JSON :=
  JSON_Object 
    [(STR_SUCCESS, JSON_Boolean false);
    (STR_PAYLOAD, (JSON_String msg))].