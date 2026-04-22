From RocqCandy Require Import All.
From CoplandSpec Require Import Attestation_Session.
From CVM Require Import IO_Utils Monad Impl.

Axiom parallel_vm_thread_axiom : forall i t e p res,
  (* parallel_vm_thread *) collect_par_subprocess i p e t = res ->
  forall st sc,
    st = {| st_trace := nil; st_evid := i |} ->
    session_plc sc = p ->
    exists st', build_cvm e t sc st = (res, st').

Axiom start_par_subprocess_axiom : forall i p e t, 
start_par_subprocess i p e t = res tt.
(*
    Definition start_par_subprocess (loc:Loc) (p:Plc) (e:Evidence) (t:Term)
    : Result unit CVM_Error. Admitted.
*)
(*
Definition collect_par_subprocess (loc:Loc) (p:Plc) (e:Evidence) (t:Term)
    : Result Evidence CVM_Error. Admitted.
*)

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
