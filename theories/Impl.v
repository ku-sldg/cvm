(*
  Implementation of the Copland Virtual Machine (CVM).
    Acts as the top-level interpreter of (core) Copland terms by dispatching to monadic helpers.
    Note:  No meaningful return type (unit).  The real work happens within the monadic state that 
    invokes services and bundles EvidenceT.

  Author:  Adam Petz, ampetz@ku.edu
*)

From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs.
From CVM Require Import Monad.

(** Monadic CVM implementation (top-level) *)
Fixpoint build_cvm (e : Evidence) (t: Term) : CVM Evidence :=
  match t with
  | asp a => do_prim e a 
  | att q t' => doRemote q e t'
  | lseq t1 t2 =>
    e1 <- build_cvm e t1 ;;cvm
    build_cvm e1 t2

  | bseq t1 t2 =>
    split_ev ;;cvm
    e1r <- build_cvm e t1 ;;cvm
    e2r <- build_cvm e t2 ;;cvm
    join_seq e1r e2r

  | bpar t1 t2 =>
    split_ev ;;cvm
    (* We will make the LOC = event_id for start of thread *)
    (* start a parallel thread working on the evidence split for t2 *)
    loc <- start_par_thread e t2 ;;cvm
    e1r <- build_cvm e t1 ;;cvm
    e2r <- wait_par_thread loc e t2 ;;cvm
    join_seq e1r e2r
  end.
