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

Definition make_network_request (ipport : IP_Port) (str : string) 
    : Result string string. Admitted.

Definition make_fs_request (path : FS_Location) (str : string) : Result string string. Admitted.

Definition aspid_to_fs_location (aspid : ASP_ID) : FS_Location. Admitted.

(** * Stub to simulate EvidenceT collected by a parallel CVM instance.
    Used by Phase 1 (sequential subprocess).  Superseded by the split
    start/collect pair below for Phase 2 (true parallel). *)
Definition parallel_vm_thread (l:Loc) (p:Plc) (e:Evidence) (t: Term) : Result Evidence CVM_Error.  Admitted.

(** * Phase 2 split-subprocess primitives.

    [start_par_subprocess] forks a subprocess CVM for term [t] (with evidence
    [e] at place [p]), writes the serialised ProtocolRunRequest to its stdin,
    and returns immediately.  The OS-level pipe fd and PID are stored in a
    CML-side global table indexed by [loc] so that [collect_par_subprocess]
    can retrieve them.

    [collect_par_subprocess] blocks until the subprocess launched at [loc]
    exits, reads its stdout, and deserialises the returned Evidence. *)
Definition start_par_subprocess (loc:Loc) (p:Plc) (e:Evidence) (t:Term)
    : CVM unit. Admitted.

Definition collect_par_subprocess (loc:Loc) (p:Plc) (e:Evidence) (t:Term)
    : Result Evidence CVM_Error. Admitted.
