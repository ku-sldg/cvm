From RocqCandy Require Import All.
Require Import IO_Axioms Monad Attestation_Session Impl.

Axiom parallel_vm_thread_axiom : forall i t e p res,
  parallel_vm_thread i p e t = res ->
  forall st sc,
    st = {| st_trace := nil; st_evid := i |} ->
    session_plc sc = p ->
    exists st', build_cvm e t sc st = (res, st').

Axiom do_remote_res_axiom : forall sc p e t res,
  do_remote sc p e t = res ->
  forall st sc' i,
    (* NOTE: This is maybe a bit stronger than we want!
    we really need to be looking at the NEW session config that was
    created via the passed session *)
    st = {| st_trace := nil; st_evid := i |} ->
    exists st',
      build_cvm e t sc st = (res, st') /\
      session_plc sc' = p /\
      session_context sc' = session_context sc.
