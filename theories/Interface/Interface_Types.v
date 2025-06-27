From RocqJSON Require Import JSON.
From CoplandSpec Require Import Term_Defs Attestation_Session.

(* Interface Types *)
Record ProtocolRunRequest := 
  mkPRReq {
    prreq_att_sess : Attestation_Session;
    prreq_req_plc: Plc;
    prreq_Evidence: Evidence;
    prreq_term: Term;
  }.

Record ProtocolRunResponse := 
  mkPRResp {
    prresp_success: bool;
    prresp_Evidence: Evidence;
  }.

Record ProtocolNegotiateRequest := 
  mkPNReq {
    pnreq_term: Term;
  }.

Record ProtocolNegotiateResponse := 
  mkPNResp {
    pnresp_success: bool;
    pnresp_term: Term;
  }.

Record ASPRunRequest := 
  mkASPRReq {
    asprreq_asp_id : ASP_ID;
    asprreq_asp_args: ASP_ARGS;
    asprreq_targ_plc : Plc ;
    asprreq_targ : TARG_ID ;
    asprreq_rawev : RawEv;
  }.

Record ASPRunResponse := 
  mkASPRResp {
    asprresp_success: bool;
    asprresp_rawev: RawEv;
  }.
