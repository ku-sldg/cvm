From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs Attestation_Session.
From CoplandManifestTools Require Import Manifest.
From CVM Require Import IO_Utils Interface.Interface AM_Manager.

Definition generate_ASP_dispatcher' (am : Manifest) (ats : Attestation_Session) (aspBin : FS_Location) (par : ASP_PARAMS) (rawEv : RawEv) : Result RawEv DispatcherErrors :=
  let (aspid, args, targ_plc, targ) := par in
  let asps := am.(asps) in
  let asp_map := am.(ASP_Mapping) in
    (* check is the ASPID is available *) 
    if (in_dec_set aspid asps)
    then 
      let conc_asp_loc := 
        match asp_map ![ aspid ] with
        | Some conc_asp_loc => conc_asp_loc
        (* If we dont find a translation, assume its the same name*)
        | None => (aspid_to_fs_location aspid)
        end 
      in
        let asp_req := (mkASPRReq aspid args targ_plc targ rawEv) in
        let js_req := to_JSON asp_req in
        let resp_res := make_JSON_FS_Location_Request aspBin conc_asp_loc js_req in
        match resp_res with
        | res js_resp =>
            match from_JSON js_resp with
            | res r => 
                let '(mkASPRResp succ bs) := r in
                res bs
            | err msg => err (Runtime msg)
            end
        | err msg => err (Runtime msg)
        end
    else err Unavailable.

(* This function will be a dispatcher for either local ASPS to CakeMLCallback, or pass them off to the ASP_Server *)
Definition generate_ASP_dispatcher `{HID : DecEq ID_Type} (am : Manifest) (al : Attestation_Session) (aspBin : FS_Location) 
    : (ASPCallback DispatcherErrors) :=
  (generate_ASP_dispatcher' am al aspBin). 

Definition session_config_compiler (conf : AM_Manager_Config) (ats : Attestation_Session) : Session_Config :=
let '(mkAM_Man_Conf man aspBin) := conf in
{|
  session_plc := (Session_Plc ats) ;
  session_context := (ats_context ats) ;
  asp_cb     := (generate_ASP_dispatcher man ats aspBin) ;
  plc_map     := (Plc_Mapping ats);
  pubkey_map  := (PubKey_Mapping ats);
  policy   := (man_policy man);
|}.

Definition session_config_decompiler (sc : Session_Config) : Attestation_Session :=
{|
  Session_Plc := (session_plc sc) ;
  Plc_Mapping := (plc_map sc) ;
  PubKey_Mapping := (pubkey_map sc) ;
  ats_context := (session_context sc)
|}.