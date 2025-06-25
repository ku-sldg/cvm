(*
Record representing the CVM Monad state structure:  cvm_st 

CVM Monad definition.

Author:  Adam Petz, ampetz@ku.edu
*)
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.

From CVM Require Export Attestation_Session.

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
Opaque CVM_Error_to_string.

Definition CVM A : Type := 
  Config Session_Config (State cvm_st (Result A CVM_Error)).

Global Create HintDb cvm.

Definition CVM_bind {A B} (m : CVM A) (f : A -> CVM B) : CVM B :=
  fun conf st => 
    let '(a, st') := m conf st in
    match a with
    | res a => f a conf st'
    | err e => ret (err e) st
    end.

Definition CVM_ret {A} (a : A) : CVM A :=
  fun _ st => (res a, st).
Definition CVM_fail {A} (e : CVM_Error) : CVM A :=
  fun _ st => (err e, st).
Definition CVM_ask : CVM Session_Config :=
  fun conf st => (res conf, st).
Definition CVM_put (st : cvm_st) : CVM unit :=
  fun _ _ => (res tt, st).
Definition CVM_get : CVM cvm_st :=
  fun _ st => (res st, st).

Global Hint Unfold CVM_bind CVM_ret CVM_ask CVM_put CVM_get CVM_fail : cvm.

Notation "x <- m ;;cvm c" := (CVM_bind m (fun x => c))
  (at level 61, m at next level, right associativity).
Notation "' pat <- m ;;cvm c" :=
  (CVM_bind m (fun x => match x with pat => c end))
  (at level 61, pat pattern, m at next level, right associativity).
Notation "e1 ;;cvm e2" := (_ <- e1 ;;cvm e2) (at level 61, right associativity).

Ltac2 Notation "cvm_monad_unfold" := ux cvm ().