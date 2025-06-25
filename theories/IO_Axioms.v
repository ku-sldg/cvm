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
From CVM Require Import Attestation_Session St.

Definition make_JSON_Network_Request (uuid : IP_Port) (js : JSON) : Result JSON string. Admitted.

Definition aspid_to_fs_location (aspid : ASP_ID) : FS_Location. Admitted.

Definition make_JSON_FS_Location_Request (dir : FS_Location) (aspid : FS_Location) (js : JSON) : Result JSON string. Admitted.

(** * Stub to simulate EvidenceT collected by a parallel CVM instance *)
Definition parallel_vm_thread (l:Loc) (p:Plc) (e:Evidence) (t: Term) : Result Evidence CVM_Error.  Admitted.

Definition do_start_par_thread (loc:Loc) (e: Evidence) (t: Term) : CVM unit :=
  CVM_ret tt.
