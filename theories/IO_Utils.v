(** Abstract definitions of IO Stub signatures.  Functions with monadic 
    return types (i.e. do_start_par_thread) should be replaced by concrete monadic 
    functions in the target language upon extraction.  Alternatively,
    if the target language does not have built-in monadic support, one can
    instantiate a non-monadic version of the stub instead.

    The non-monadic stubs (i.e. doRemote_uuid) remain abstract (Admitted) in Coq 
    because they are either too low-level to reason about, or require external 
    IO capabilities not modeled first-class in our spec.  The abstract binary
    and EvidenceT value results support specification of correctness properties 
    for Appraisal.        
 *)
From CoplandSpec Require Import Term_Defs.
From RocqCandy Require Import StateMonad.
From CVM Require Import St.
From CVM Require Export IO_Axioms.

Definition make_JSON_Network_Request (ipport : IP_Port) (js : JSON) 
    : Result JSON string :=
  resstr <- make_network_request ipport (to_string js) ;;
  from_string resstr.

Definition fs_location_join (dir : FS_Location) (tail : FS_Location) : FS_Location :=
  dir ++ "/" ++ tail.

Definition make_JSON_FS_Location_Request (dir : FS_Location) (aspid : FS_Location) (js : JSON) : Result JSON string :=
  resstr <- make_fs_request (fs_location_join dir aspid) (to_string js) ;;
  from_string resstr.

Definition do_start_par_thread (loc:Loc) (e: Evidence) (t: Term) : CVM unit :=
  CVM_ret tt.
