(*
Record representing the CVM Monad state structure:  cvm_st 

CVM Monad definition.

Author:  Adam Petz, ampetz@ku.edu
*)
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.

From CVM Require Import Attestation_Session.

(** CVM monad state structure.

    st_ev - EvidenceT bundle.  Holds raw EvidenceT sequence along with its 
            EvidenceT Type.
    st_trace - Event trace accumulated by the CVM (relevant only during 
               verification)
    st_pl - Current "executing place".
    st_evid - Monotonic event ID counter.  Incremented after each 
              attestation-relevant event/invocation.
    st_config - AM Configuration (typically produced by the Manifest Compiler).  
                   Provides callback functions used by the CVM to interpret Copland.
 *)


Record cvm_st : Type := mk_st {
  st_trace  : list Ev ;
  st_evid   : Event_ID ;
}.

Inductive CVM_Error : Type := 
| at_error_static : Term -> Plc -> Evidence -> CVM_Error
| at_error_dynamic : Term -> IP_Port -> Evidence -> CVM_Error
| dispatch_error : DispatcherErrors -> CVM_Error.
(* | callback_error : CallBackErrors -> CVM_Error. *)

Definition CVM_Error_to_string (e : CVM_Error) : string :=
  match e with
  | at_error_static t p e => "at_error_static"
  | at_error_dynamic t u e => "at_error_dynamic"
  | dispatch_error de => 
    match de with
    | Unavailable => "dispatch_error: Unavailable"
    | Runtime s => "dispatch_error: " ++ s
    end
  end.

Definition CVM A : Type := State (cvm_st * Session_Config) A CVM_Error.
