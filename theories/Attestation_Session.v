From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs_Core.
From CVM Require Import System_Types.
(* Require Import JSON Interface_Strings_Vars. *)

Record Attestation_Session := {
  Session_Plc     : Plc ;
  Plc_Mapping     : Map Plc IP_Port;
  PubKey_Mapping  : Map Plc Public_Key;
  ats_context     : GlobalContext
}.

Inductive DispatcherErrors : Type :=
| Unavailable   : DispatcherErrors
| Runtime       : string -> DispatcherErrors.

Inductive CallBackErrors : Type := 
| messageLift   : string -> CallBackErrors.

Definition ASPCallback (ErrType : Type) : Type := 
  ASP_PARAMS -> RawEv -> Result RawEv ErrType.

Definition PolicyT := list (Plc * ASP_ID).

Record Session_Config := {
  session_plc         : Plc ;
  session_context     : GlobalContext ;
  asp_cb              : ASPCallback DispatcherErrors ;
  plc_map             : Map Plc IP_Port ;
  pubkey_map          : Map Plc Public_Key ;
  policy              : PolicyT ;
}.

Open Scope string_scope.
Global Instance Jsonifiable_Attestation_Session `{Jsonifiable (Map Plc IP_Port), Jsonifiable (Map Plc PublicKey), Jsonifiable GlobalContext}: Jsonifiable Attestation_Session.
eapply Build_Jsonifiable with 
  (to_JSON := (fun v => 
                JSON_Object [
                  (STR_Session_Plc, JSON_String (to_string (Session_Plc v)));
                  (STR_Plc_Mapping, to_JSON (Plc_Mapping v));
                  (STR_PubKey_Mapping, to_JSON (PubKey_Mapping v));
                  (STR_Session_Context, to_JSON (ats_context v))])) 
  (from_JSON := (fun j =>
    plc <- JSON_get_string STR_Session_Plc j ;;
    plc_map <- JSON_get_Object STR_Plc_Mapping j ;;
    pub_map <- JSON_get_Object STR_PubKey_Mapping j ;;
    sc <- JSON_get_Object STR_Session_Context j ;;
    plc' <- from_string plc ;;
    plc_map' <- from_JSON plc_map ;;
    pub_map' <- from_JSON pub_map ;;
    sc <- from_JSON sc ;;
    resultC {| Session_Plc := plc'; Plc_Mapping := plc_map'; PubKey_Mapping := pub_map'; ats_context := sc |})); solve_json.
Defined.