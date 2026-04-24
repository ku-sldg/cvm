From RocqCandy Require Import All.
From CoplandSpec Require Import Attestation_Session.
From CVM Require Import IO_Utils Monad Impl.

Axiom parallel_vm_thread_axiom : forall i t e p res,
  (* parallel_vm_thread *) collect_par_subprocess i p e t = res ->
  forall st (sc : CVM_Config),
    st = {| st_trace := nil; st_evid := i |} ->
    session_plc (cc_session sc) = p ->
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

Axiom do_remote_res_axiom : forall (cfg : CVM_Config) p e t res,
  do_remote (cc_session cfg) p e t = res ->
  forall st i,
    st = {| st_trace := nil; st_evid := i |} ->
    exists (cfg' : CVM_Config) st',
      build_cvm e t cfg' st = (res, st') /\
      session_plc (cc_session cfg') = p /\
      session_context (cc_session cfg') = session_context (cc_session cfg).
