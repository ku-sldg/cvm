(* This file is the main verification for the Copland Virtual Machine (CVM) 

  In this file we prove the following properties:
  1. Determinicity of CVM Evidence ("cvm_deterministic_Evidence")
  (two CVMs that start with the same Configuration and Evidence will yield the same result Evidence when run on the same term)

  2. Preservation of Evidence Well Typedness ("cvm_preserves_wf_Evidence")
  (any CVM that receives well-typed Evidence and executes to completion without an error will return well-typed Evidence)

  3. Good Evidence type ("cvm_evidence_type")
  (any CVM that executed to completion without errors will yield Evidence that respects the eval evidence function)

  4. CVM respects Events ("cvm_trace_respects_events")
  (any CVM that executes to completion without an error will have a trace that accurately reflects the Event semantics that have been laid out)

*)
From RocqCandy Require Import All.
From CoplandSpec Require Import Term_Defs Event_System Attestation_Session
  TypeSys TypeSys_Eval.
From CVM Require Import Impl St Monad Cvm_Axioms.
From Equations Require Import Equations.
Local Open Scope list_scope.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2,
  peel_n_rawev n ls = res (ls1, ls2) ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; ff with u, a.
Qed.

Lemma peel_n_none_spec : forall n ls e,
  peel_n_rawev n ls = err e ->
  length ls < n.
Proof.
  induction n; ff with u, a, l.
Qed.

Lemma invoke_APPR_deterministic : forall G e sc st1 st2 st1' st2' res1 res2 r oe,
  G = session_context sc ->
  st_evid st1 = st_evid st2 ->
  invoke_APPR' r e oe sc st1 = (res1, st1') ->
  invoke_APPR' r e oe sc st2 = (res2, st2') ->
  res1 = res2 /\ st_evid st1' = st_evid st2'.
Proof.
  intros G.
  induction e;
  simpl in *; intros sc st1 st2 st1' st2' res1 res2 r oe HG Hst Hr1 Hr2;
  try (ux cvm (); intuition; repeat find_injection; eauto; fail).
  - ff with (ux cvm ()).
  - ux cvm ();
    target_break_match Hr1; ff;
    try (Control.enter (fun () =>
    match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end)).
  - cvm_monad_unfold;
    target_break_match Hr1;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match Hr2);
    repeat (match! goal with
      | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
          h2 : invoke_APPR' _ ?_e _ _ _ = _,
          ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
        let h2 := Control.hyp h2 in
        let ih := Control.hyp ih in
        eapply $ih in $h1 > [ | | | eapply $h2]; ff
      end).
Qed.

Theorem invoke_APPR_deterministic_Evidence : forall G et st1 st2 r1 r2 st1' st2' r sc eo,
  G = session_context sc ->
  invoke_APPR' r et eo sc st1 = (r1, st1') ->
  invoke_APPR' r et eo sc st2 = (r2, st2') ->
  r1 = r2.
Proof.
  intros G.
  induction et;
  intros st1 st2 r1 r2 st1' st2' r sc eo HG Hr1 Hr2;
  simpl in *; subst; cvm_monad_unfold;
  try (repeat find_injection; reflexivity).
  - target_break_match Hr1.
  - target_break_match Hr1;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match Hr2);
    Control.enter (fun () =>
    repeat (match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end)).
  - target_break_match Hr1;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match Hr2);
    Control.enter (fun () =>
    repeat (match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end)).
Qed.

Lemma cvm_deterministic :  forall t e sc st1 st2 r1 r2 st1' st2',
  st_evid st1 = st_evid st2 ->
  build_cvm e t sc st1 = (r1, st1') ->
  build_cvm e t sc st2 = (r2, st2') ->
  (r1 = r2) /\ (st_evid st1' = st_evid st2').
Proof.
  induction t; ff with (cvm_monad_unfold);
  repeat (match! goal with
  | [ u : unit |- _ ] => 
    let u := Control.hyp u in
    destruct $u
  | [ h1 : build_cvm _ ?_t _ _ = _,
      h2 : build_cvm _ ?_t _ _ = _,
      ih : context[build_cvm _ ?_t _ _ = _ -> _] |- _ ] =>
      let h2v := Control.hyp h2 in
      let ihv := Control.hyp ih in
      eapply $ihv in $h1 > [ | | eapply $h2v ]; ff;
      try (clear $ih $h2)
  end);
  try (  solve [ eapply invoke_APPR_deterministic; ff ]).
Qed.

Lemma appr_events'_errs_deterministic : forall G p e e' i1 e1,
  appr_events' G p e e' i1 = err e1 ->
  forall i2, appr_events' G p e e' i2 = err e1.
Proof.
  intros G.
  induction e;
  intros; simpl in *; ff with u, (a);
  try (find_eapply_lem_hyp IHe; ff; fail);
  try (find_eapply_lem_hyp IHe1; ff);
  try (find_eapply_lem_hyp IHe2; ff).
Qed.

Lemma asp_events_errs_deterministic : forall G t p e i1 i2 e1 e2,
  asp_events G p e t i1 = res e1 ->
  asp_events G p e t i2 = err e2 ->
  False.
Proof.
  destruct t; ff; try (destruct e; simpl in *; congruence);
  find_eapply_lem_hyp appr_events'_errs_deterministic; ff.
  unfold appr_events in *; simpl in *; ff.
Qed.

Lemma events_fix_errs_deterministic : forall G t p e i1 i2 e1 e2,
  events_fix G p e t i1 = res e1 ->
  events_fix G p e t i2 = err e2 ->
  False.
Proof.
  induction t; ff with u, a;
  eapply asp_events_errs_deterministic; eauto.
Qed.

Lemma events_fix_only_one_error : forall G t p e i1 i2 e1 e2,
  events_fix G p e t i1 = err e1 ->
  events_fix G p e t i2 = err e2 ->
  e1 = e2.
Proof.
  induction t; ff with u, a;
  try (match! goal with
  | [ h1 : events_fix _ _ _ ?_t _ = res _,
      h2 : events_fix _ _ _ ?_t _ = err _ |- _ ] =>
    let h2 := Control.hyp h2 in
    eapply events_fix_errs_deterministic in $h1; try (eapply $h2); ff
  end);
  destruct a; simpl in *;
  try (destruct e; simpl in *; congruence);
  find_eapply_lem_hyp appr_events'_errs_deterministic; 
  unfold appr_events in *; ff.
Qed.

Theorem cvm_deterministic_Evidence : forall t e sc st1 st2 r1 r2 st1' st2',
  build_cvm e t sc st1 = (r1, st1') ->
  build_cvm e t sc st2 = (r2, st2') ->
  r1 = r2.
Proof.
  induction t; simpl in *; cvm_monad_unfold.
  - ff; eapply invoke_APPR_deterministic_Evidence; eauto.
  - ff; (* NOTE: Why dont we need the remote axiom here!? *)
    Control.enter (fun () =>
    match! goal with
    | [ h1 : events_fix _ _ _ ?_t _ = _,
        h2 : events_fix _ _ _ ?_t _ = _ |- _ ] =>
      let h2 := Control.hyp h2 in
      try (eapply events_fix_only_one_error in $h1; try (eapply $h2); ff; eauto; fail);
      try (eapply events_fix_errs_deterministic in $h1; try (eapply $h2); ff; eauto; fail)
    end).
  - ff; Control.enter (fun () => repeat (match! goal with
    | [ u : unit |- _ ] => 
      let u := Control.hyp u in
      destruct $u
    | [ h1 : build_cvm _ ?_t _ _ = _,
        h2 : build_cvm _ ?_t _ _ = _,
        ih : context[build_cvm _ ?_t _ _ = _ -> _] |- _ ] =>
        let h2v := Control.hyp h2 in
        let ihv := Control.hyp ih in
        simpl in *; ff;
        eapply $ihv in $h1 > [ | eapply $h2v];
        clear $ih $h2; ff
    end)).
  - ff; Control.enter (fun () => repeat (match! goal with
    | [ h1 : build_cvm _ ?_t _ _ = _,
        h2 : build_cvm _ ?_t _ _ = _,
        ih : context[build_cvm _ ?_t _ _ = _ -> _] |- _ ] =>
        let h2v := Control.hyp h2 in
        let ihv := Control.hyp ih in
        simpl in *; ff;
        eapply $ihv in $h1 > [ | eapply $h2v];
        clear $ih $h2; ff
    end)).
  - ff; try (
    repeat (match! goal with
    | [ h : parallel_vm_thread _ _ _ _ = ?_res |- _ ] =>
      eapply parallel_vm_thread_axiom in $h; ff
    | [ h1 : build_cvm _ ?_t _ _ = _,
        h2 : build_cvm _ ?_t _ _ = _,
        ih : context[build_cvm _ ?_t _ _ = _ -> _] |- _ ] =>
        let h2v := Control.hyp h2 in
        let ihv := Control.hyp ih in
        eapply $ihv in $h1 > [ | eapply $h2v];
        clear $ih $h2; ff
    end);
    try (match! goal with
    | [ h1 : events_fix _ _ _ ?_t _ = _,
        h2 : events_fix _ _ _ ?_t _ = _ |- _ ] =>
      let h2 := Control.hyp h2 in
      try (eapply events_fix_only_one_error in $h1; try (eapply $h2); ff; try eauto; fail);
      try (eapply events_fix_errs_deterministic in $h1; try (eapply $h2); ff; try eauto; fail)
    end); fail).
Qed.

Lemma invoke_APPR'_spans : forall G' et r e' sc c i st eo,
  G' = session_context sc ->
  invoke_APPR' r et eo sc st = (res e', c) ->
  forall G,
  G = session_context sc ->
  appr_events_size G et = res i ->
  st_evid c = st_evid st + i.
Proof.
  intros G'.
  induction et;
  ff with u, (ux cvm ()), a;
  repeat (match! goal with
  | [ h : invoke_APPR' _ ?_e _ _ _ = _,
      ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
    let ih := Control.hyp ih in
    eapply $ih in $h; ff with l;
    try lia
  end).
Qed.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
| et_same_asps_mt : et_same_asps mt_evt mt_evt
| et_same_asps_nonce : forall n1 n2, et_same_asps (nonce_evt n1) (nonce_evt n2)
| et_same_asps_asp : forall p1 p2 e1 e2 aid args1 args2,
    et_same_asps e1 e2 ->
    et_same_asps 
      (asp_evt p1 (asp_paramsC aid args1) e1) 
      (asp_evt p2 (asp_paramsC aid args2) e2)
| et_same_asps_left : forall e1 e2,
    et_same_asps e1 e2 ->
    et_same_asps (left_evt e1) (left_evt e2)
| et_same_asps_right : forall e1 e2,
    et_same_asps e1 e2 ->
    et_same_asps (right_evt e1) (right_evt e2)
| et_same_asps_split : forall e1 e2 e1' e2',
    et_same_asps e1 e2 ->
    et_same_asps e1' e2' ->
    et_same_asps (split_evt e1 e1') (split_evt e2 e2').
Local Hint Constructors et_same_asps : et_same_asps_db.

Lemma et_same_asps_refl : forall e,
  et_same_asps e e.
Proof.
  induction e; eauto using et_same_asps;
  repeat (match! goal with
  | [ a : ASP_PARAMS |- _ ] => 
    let a := Control.hyp a in
    destruct $a; eauto using et_same_asps
  end).
Qed.
Local Hint Resolve et_same_asps_refl : et_same_asps_db.

Lemma et_same_asps_ev_path_left : forall e1 e2,
  et_same_asps e1 e2 ->
  forall ep,
  et_same_asps (proc_ev_path_left ep e1) (proc_ev_path_left ep e2).
Proof.
  destruct ep; eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_ev_path_left : et_same_asps_db.

Lemma et_same_asps_ev_path_right : forall e1 e2,
  et_same_asps e1 e2 ->
  forall ep,
  et_same_asps (proc_ev_path_right ep e1) (proc_ev_path_right ep e2).
Proof.
  destruct ep; eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_ev_path_right : et_same_asps_db.

Lemma et_same_asps_symm : forall e1 e2,
  et_same_asps e1 e2 -> et_same_asps e2 e1.
Proof.
  intros.
  prep_induction H.
  induction H; eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_symm : et_same_asps_db.

(* [normalize_ev] depends only on the ASP structure (aids) and [G], not on the
   places / args / nonce-ids that [et_same_asps] abstracts over, so it preserves
   [et_same_asps]. Needed because [appr_procedure] now normalizes its structural
   argument before recursing. *)
Lemma et_same_asps_normalize_ev : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_same_asps (normalize_ev G e1) (normalize_ev G e2).
Proof.
  intros G e1 e2 H.
  induction H; ltac1:(simp normalize_ev); eauto using et_same_asps.
  - (* asp: same aid; the normalized inner drives the same branch on both sides *)
    destruct (normalize_ev G e1) eqn:E1; destruct (normalize_ev G e2) eqn:E2;
    inversion IHet_same_asps; subst; simpl in *;
    eauto using et_same_asps; ff with u, a; eauto using et_same_asps.
  - (* left projection *)
    destruct (normalize_ev G e1) eqn:E1; destruct (normalize_ev G e2) eqn:E2;
    inversion IHet_same_asps; subst; simpl in *;
    eauto using et_same_asps.
  - (* right projection *)
    destruct (normalize_ev G e1) eqn:E1; destruct (normalize_ev G e2) eqn:E2;
    inversion IHet_same_asps; subst; simpl in *;
    eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_normalize_ev : et_same_asps_db.

(* [et_size_canon] only consults ASP ids (via [asp_types G]) and the evidence
   shape, both preserved by [et_same_asps]. *)
Lemma et_size_canon_same_asps : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size_canon G e1 = et_size_canon G e2.
Proof.
  intros G e1 e2 H.
  induction H; try reflexivity.
  - (* asp: same aid, so the type-signature lookup agrees; only EXTEND recurses *)
    rewrite et_size_canon_asp_unfold.
    rewrite et_size_canon_asp_unfold.
    rewrite IHet_same_asps.
    reflexivity.
  - (* split *)
    rewrite et_size_canon_split_unfold.
    rewrite et_size_canon_split_unfold.
    rewrite IHet_same_asps1.
    rewrite IHet_same_asps2.
    reflexivity.
Qed.

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros G e1 e2 H.
  unfold et_size.
  apply et_size_canon_same_asps.
  apply et_same_asps_normalize_ev.
  exact H.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : et_same_asps_db.

Lemma et_same_asps_asp_dir : forall e1 e2 asp_id args1 args2 p1 p2 par1 par2,
  et_same_asps e1 e2 ->
  par1 = (asp_paramsC asp_id args1) ->
  par2 = (asp_paramsC asp_id args2) ->
  et_same_asps (asp_evt p1 par1 e1) (asp_evt p2 par2 e2).
Proof.
  intros.
  prep_induction H.
  induction H; intros; subst_max; eauto using et_same_asps;
  try (econstructor; eapply et_same_asps_refl; fail).
Qed.
Local Hint Resolve et_same_asps_asp_dir : et_same_asps_db.

Lemma equiv_EvidenceT_impl_et_size_same : forall G e1 e2,
  equiv_EvidenceT G e1 e2 = true ->
  et_size G e1 = et_size G e2.
Proof.
  intros.
  unfold equiv_EvidenceT in *; ff with u, a.
Qed.

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2 e1o e2o,
  et_same_asps e1 e2 ->
  et_same_asps e1o e2o ->
  appr_procedure' G p1 e1 e1o = res e1' ->
  appr_procedure' G p2 e2 e2o = res e2' ->
  et_same_asps e1' e2'.
Proof.
  intros G.
  induction e1; intros e1' e2 e2' p1 p2 e1o e2o Hsame Hsameo Hr1 Hr2;
  invc Hsame; simpl in *; cvm_monad_unfold; ff with u, a;
  try (econstructor; eauto using et_same_asps; fail).
  (* WRAP: recurse under the cancelling dual, with the dual-extended output
     accumulators still related *)
  eapply IHe1 > [ exact H3 | | exact Hr1 | exact Hr2 ].
  econstructor; exact Hsameo.
Qed.
Local Hint Resolve et_same_asps_appr_procedure : et_same_asps_db.

(* [appr_procedure] (which normalizes its structural argument) preserves
   [et_same_asps], lifting [et_same_asps_appr_procedure] over [appr_procedure']. *)
Lemma et_same_asps_appr_procedure_full : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = res e1' ->
  appr_procedure G p2 e2 = res e2' ->
  et_same_asps e1' e2'.
Proof.
  intros G e1 e1' e2 e2' p1 p2 Hsame H1 H2.
  unfold appr_procedure in *.
  eapply et_same_asps_appr_procedure >
    [ eapply et_same_asps_normalize_ev; exact Hsame
    | exact Hsame | exact H1 | exact H2 ].
Qed.
Local Hint Resolve et_same_asps_appr_procedure_full : et_same_asps_db.

Lemma et_same_asps_eval_same_asps : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = res e1' ->
  eval G p2 e2 t = res e2' ->
  et_same_asps e1' e2'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; ff; eauto using et_same_asps.
    eapply et_same_asps_appr_procedure_full; eauto.
  - ff with u, a.
  - ff with u, a.
    repeat (match! goal with
    | [ h1 : eval _ ?_p1 ?_e1 ?_t = res ?_e1',
        h2 : eval _ ?_p2 ?_e2 ?_t = res ?_e2',
        ih : context[eval _ _ _ ?_t = _ -> _] |- _ ] =>
      let h1v := Control.hyp h1 in
      let ih := Control.hyp ih in
      eapply $ih in $h2; try (eapply $h1v); 
      clear $h1
    end); ff; eauto with et_same_asps_db.
  - ff with u, a.
    repeat (match! goal with
    | [ h1 : eval _ ?_p1 ?_e1 ?_t = res ?_e1',
        h2 : eval _ ?_p2 ?_e2 ?_t = res ?_e2',
        ih : context[eval _ _ _ ?_t = _ -> _] |- _ ] =>
      let h1v := Control.hyp h1 in
      let ih := Control.hyp ih in
      eapply $ih in $h2; try (eapply $h1v); 
      clear $h1
    end); ff; eauto with et_same_asps_db.
Qed.
Local Hint Resolve et_same_asps_eval_same_asps : et_same_asps_db.

Lemma appr_procedure_et_size_plc_irrel : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = res e1' ->
  appr_procedure G p2 e2 = res e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto with et_same_asps_db.
Qed.

Lemma eval_et_size_plc_irrel : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = res e1' ->
  eval G p2 e2 t = res e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto with et_same_asps_db.
Qed.

Lemma et_same_asps_impl_appr_events_size_same : forall G e1 e2 n1 n2,
  et_same_asps e1 e2 ->
  appr_events_size G e1 = res n1 ->
  appr_events_size G e2 = res n2 ->
  n1 = n2.
Proof.
  intros G.
  induction e1; intros; simpl in *; ff with u, a;
  try (invc H; ff with u, a; fail).
  - invc H; ff with u, a.
    find_eapply_lem_hyp IHe1_1; try (reflexivity); ff.
Qed.

Lemma events_size_eval_res_irrel : forall G t1 t p1 p2 et e1 e2 n1 n2,
  eval G p1 et t1 = res e1 ->
  eval G p2 et t1 = res e2 ->
  events_size G p1 e1 t = res n1 ->
  events_size G p2 e2 t = res n2 ->
  n1 = n2.
Proof.
  intros.
  assert (et_same_asps e1 e2) by (
    assert (et_same_asps et et) by (eapply et_same_asps_refl);
    eauto with et_same_asps_db
  );
  clear H H0 et.
  generalizeEverythingElse t.
  induction t; simpl in *; intuition; ff with u, a;
  eauto with et_same_asps_db.
  - eapply et_same_asps_impl_appr_events_size_same >
    [ eapply et_same_asps_normalize_ev; eassumption | eassumption | eassumption ].
  - simpl in *; ff with u, a;
    repeat (match! goal with
    | [ h1 : events_size _ ?_p1 ?_e1 ?_t1 = _,
        h2 : events_size _ ?_p2 ?_e2 ?_t1 = _,
        ih : context[events_size _ _ _ ?_t1 = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2v := Control.hyp h2 in
      eapply $ih in $h1; try (eapply $h2v);
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; eauto; fail);
      clear $h2; ff
    end); eauto with et_same_asps_db.
  - simpl in *; ff with u, a;
    repeat (match! goal with
    | [ h1 : events_size _ ?_p1 ?_e1 ?_t1 = _,
        h2 : events_size _ ?_p2 ?_e2 ?_t1 = _,
        ih : context[events_size _ _ _ ?_t1 = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2v := Control.hyp h2 in
      eapply $ih in $h1; try (eapply $h2v);
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; eauto; fail);
      clear $h2; ff
    end); eauto with et_same_asps_db.
Qed.

Lemma events_size_plc_irrel : forall G t et p1 p2 n1 n2,
  events_size G p1 et t = res n1 ->
  events_size G p2 et t = res n2 ->
  n1 = n2.
Proof.
  induction t; simpl in *; intuition; ff with u, a;
  repeat (match! goal with
  | [ h1 : events_size _ _ _ ?_t = _,
      h2 : events_size _ _ _ ?_t = _,
      ih : context[events_size _ _ _ ?_t] |- _ ] =>
    let ih := Control.hyp ih in
    let h2v := Control.hyp h2 in
    eapply $ih in $h1 > [ | eapply $h2v ];
    clear $h2; ff
  end); try lia.
  - eapply events_size_eval_res_irrel in Heq4; ff.
Qed.

Definition well_formed_context (G : GlobalContext) : Prop :=
  (asp_types G) ![ sig_aspid ] 
    = Some (ev_arrow (EXTEND (exist _ 1 Nat.lt_0_1) InAll) []) /\
  (asp_types G) ![ hsh_aspid ] 
    = Some (ev_arrow (REPLACE (exist _ 1 Nat.lt_0_1)) []) /\
  (asp_types G) ![ enc_aspid ] = Some (ev_arrow (WRAP (exist _ 1 Nat.lt_0_1)) []) /\
  (asp_types G) ![ check_nonce_aspid ] 
    = Some (ev_arrow (EXTEND (exist _ 1 Nat.lt_0_1) InAll) []).

Lemma invoke_ASP_evidence : forall e par st sc e' st',
  invoke_ASP e par sc st = (res e', st') ->
  get_et e' = asp_evt (session_plc sc) par (get_et e).
Proof.
  cvm_monad_unfold; ff.
Qed.

Theorem invoke_APPR'_evidence : forall G et st r sc st' e' e eo,
  G = session_context sc ->
  invoke_APPR' r et eo sc st = (res e', st') ->
  appr_procedure' (session_context sc) (session_plc sc) et eo = res e ->
  get_et e' = e.
Proof.
  intros G.
  induction et;
  intuition; simpl in *.
  - ff with (cvm_monad_unfold).
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff with u, a.
    cvm_monad_unfold; ff.
    all: find_eapply_lem_hyp IHet; ff; simpl in *; ff.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff with u;
    cvm_monad_unfold; ff with u, a.
    repeat (match! goal with
    | [ h1 : invoke_APPR' _ ?_e ?_o _ _ = _,
        h2 : appr_procedure' _ _ ?_e ?_o = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2 := Control.hyp h2 in
      eapply $ih in $h1; try (eapply $h2); ff
    end).
Qed.

Theorem cvm_evidence_type : forall t e e' st st' sc et',
  build_cvm e t sc st = (res e', st') ->
  eval (session_context sc) (session_plc sc) (get_et e) t = res et' ->
  get_et e' = et'.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; destruct a; simpl in *;
    repeat find_injection; simpl in *; try congruence;
    unfold well_formed_context in *; simpl in *; 
    ff; repeat find_rewrite; simpl in *; eauto.
    eapply invoke_APPR'_evidence in H; ff.
  - cvm_monad_unfold; ff.
    find_eapply_lem_hyp do_remote_res_axiom; ff.
    find_eapply_lem_hyp IHt; ff.
  - ff with u, a; cvm_monad_unfold; ff;
    try (match! goal with
    | [ h1 : build_cvm _ ?_t1 _ _ = _,
        h2 : build_cvm _ ?_t2 _ _ = _,
        ih1 : context[build_cvm _ ?_t1 _ _ = _ -> _],
        ih2 : context[build_cvm _ ?_t2 _ _ = _ -> _] |- _ ] =>
      let ih1 := Control.hyp ih1 in
      let ih2 := Control.hyp ih2 in
      eapply $ih1 in $h1 as ?; ff;
      eapply $ih2 in $h2; ff
    end).
  - ff with u, a; cvm_monad_unfold; ff.
    destruct e;
    find_eapply_lem_hyp IHt1; ff;
    find_eapply_lem_hyp IHt2; ff.
  - ff with u, a; cvm_monad_unfold; ff;
    find_eapply_lem_hyp parallel_vm_thread_axiom; eauto; ff with u, a;
    try (unfold mt_evc in *; ff);
    destruct e;
    find_eapply_lem_hyp IHt1; ff;
    find_eapply_lem_hyp IHt2; ff.
    Unshelve. eapply 0.
Qed.

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t st e st' sc i e',
  well_formed_context (session_context sc) ->
  build_cvm e t sc st = (res e', st') ->
  events_size (session_context sc) (session_plc sc) (get_et e) t = res i ->
  st_evid st' = st_evid st + i.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; ff.
    find_eapply_lem_hyp invoke_APPR'_spans; ff.
  - cvm_monad_unfold; ff with u;
    find_eapply_lem_hyp events_size_plc_irrel;
    try (eapply Heq5); ff with l.
  - cvm_monad_unfold; ff with u.

    match! goal with
    | [ h : build_cvm _ ?_t _ _ = _,
        h1 : events_size _ _ _ ?_t = _,
        ih : context[build_cvm _ ?_t _ _ = _ -> _] |- _ ] => 
      let ihv := Control.hyp ih in
      let h1v := Control.hyp h1 in
      eapply $ihv in $h as ? > [ | | eapply $h1v]; ff;
      try (eapply cvm_evidence_type in $h as ?; ff);
      clear $h $ih
    end.
    find_eapply_lem_hyp IHt2; ff with l.
  - cvm_monad_unfold; ff with u, a.
    destruct e;
    find_eapply_lem_hyp IHt1; ff;
    find_eapply_lem_hyp IHt2; ff with l.
  - ff with u, a, (cvm_monad_unfold).
    destruct e;
    find_eapply_lem_hyp IHt1; ff with l.
Qed.

(* Read the size equation off a [wf_Evidence] witness. *)
Lemma wf_Evidence_inv : forall G r et,
  wf_Evidence G (evc r et) ->
  et_size G et = res (List.length r).
Proof.
  intros G r et H.
  invc H.
  assumption.
Qed.

Lemma wf_Evidence_split : forall G r1 r2 et1 et2,
  wf_Evidence G (evc r1 et1) ->
  wf_Evidence G (evc r2 et2) ->
  wf_Evidence G (evc (r1 ++ r2) (split_evt et1 et2)).
Proof.
  intros G r1 r2 et1 et2 Hwf1 Hwf2.
  eapply wf_Evidence_inv in Hwf1.
  eapply wf_Evidence_inv in Hwf2.
  econstructor.
  - rewrite length_app.
    reflexivity.
  - rewrite et_size_split.
    rewrite Hwf1.
    rewrite Hwf2.
    reflexivity.
Qed.
Local Hint Resolve wf_Evidence_split : wf_Evidence.

Lemma wf_Evidence_impl_et_size_res : forall G e,
  wf_Evidence G e ->
  exists n, et_size G (get_et e) = res n.
Proof.
  intros G e H.
  destruct e as [r et].
  eapply wf_Evidence_inv in H.
  exists (List.length r).
  exact H.
Qed.

Lemma wf_Evidence_mt_evc : forall G,
  wf_Evidence G mt_evc.
Proof.
  intros G.
  unfold mt_evc.
  econstructor.
  - reflexivity.
  - exact (et_size_mt G).
Qed.

Fixpoint meta_machinery_pad_n (n : nat) (e : RawEv) : RawEv :=
  match n with
  | 0 => e
  | S n' => passed_bs :: meta_machinery_pad_n n' e
  end.

Lemma meta_machinery_pad_n_size : forall n e,
  List.length (meta_machinery_pad_n n e) = n + List.length e.
Proof.
  induction n; ff.
Qed.

Lemma wf_Evidence_exists : forall G e n,
  et_size G e = res n ->
  exists r, wf_Evidence G (evc r e).
Proof.
  intros G e n Hsz.
  exists (meta_machinery_pad_n n nil).
  econstructor.
  - reflexivity.
  - rewrite Hsz.
    rewrite meta_machinery_pad_n_size.
    simpl.
    f_equal.
    lia.
Qed.

(* Normalizing the evidence type preserves wf ([et_size] is normalize-invariant). *)
Lemma wf_Evidence_normalize_ev : forall G r et,
  wf_Evidence G (evc r et) ->
  wf_Evidence G (evc r (normalize_ev G et)).
Proof.
  intros G r et Hwf.
  eapply wf_Evidence_inv in Hwf.
  econstructor.
  - reflexivity.
  - rewrite <- et_size_normalize.
    exact Hwf.
Qed.

(* Every branch of [bundle_asp] checks the length of the raw evidence it bundles
   against the size its output type prescribes, so its outputs are wf. *)
Lemma wf_Evidence_bundle_asp : forall sc p rwev cur_ev ps st e' st',
  wf_Evidence (session_context sc) cur_ev ->
  bundle_asp p rwev cur_ev ps sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  intros sc p rwev cur_ev ps st e' st' Hwf Hbun.
  destruct ps as [asp_id args].
  destruct cur_ev as [bits et0].
  eapply wf_Evidence_inv in Hwf.
  cbv beta iota zeta delta [bundle_asp get_asp_type get_config hoist_result
    hoist_option CVM_bind CVM_ret CVM_fail CVM_ask get_et ret] in Hbun.
  destruct ((asp_types (session_context sc)) ![ asp_id ]) as [ [fwd attrs] | ] eqn:Hlk >
  [ | inversion Hbun ].
  destruct fwd as [ [n nlt] | [n nlt] | | [n nlt] isig ].
  - (* REPLACE: length checked against the REPLACE size *)
    destruct (DecEq.dec_eq (List.length rwev) n) as [Hlen | Hne] > [ | inversion Hbun ].
    inversion Hbun; subst.
    econstructor.
    + reflexivity.
    + erewrite et_size_asp_replace > [ reflexivity | exact Hlk ].
  - (* WRAP: same shape as REPLACE *)
    destruct (DecEq.dec_eq (List.length rwev) n) as [Hlen | Hne] > [ | inversion Hbun ].
    inversion Hbun; subst.
    econstructor.
    + reflexivity.
    + erewrite et_size_asp_wrap > [ reflexivity | exact Hlk ].
  - (* UNWRAP: length checked against [et_size] of the bundled output type *)
    destruct (et_size (session_context sc) (asp_evt p (asp_paramsC asp_id args) et0))
      as [size | ] eqn:Hsz > [ | inversion Hbun ].
    destruct (DecEq.dec_eq (List.length rwev) size) as [Hlen | Hne] > [ | inversion Hbun ].
    inversion Hbun; subst.
    econstructor.
    + reflexivity.
    + exact Hsz.
  - (* EXTEND: the new bits extend the (wf) current bundle *)
    destruct (DecEq.dec_eq (List.length rwev) n) as [Hlen | Hne] > [ | inversion Hbun ].
    inversion Hbun; subst.
    econstructor.
    + rewrite length_app.
      reflexivity.
    + erewrite et_size_asp_extend > [ | exact Hlk ].
      rewrite Hwf.
      reflexivity.
Qed.

(* [invoke_ASP] = tag + external call + [bundle_asp]; wf flows through the
   bundling checks regardless of what raw evidence the ASP callback returns. *)
Lemma wf_Evidence_invoke_ASP : forall sc e ps st e' st',
  wf_Evidence (session_context sc) e ->
  invoke_ASP e ps sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  intros sc e ps st e' st' Hwf Hrun.
  cbv beta iota zeta delta [invoke_ASP get_pl tag_ASP inc_id add_trace get_trace
    get_evid get_st put_trace do_asp get_config CVM_bind CVM_ret CVM_fail
    CVM_ask CVM_put CVM_get ret] in Hrun.
  destruct (asp_cb sc ps (get_bits e)) as [rawev | derr] eqn:Hcb > [ | inversion Hrun ].
  match! goal with
  | [ _h : context [ bundle_asp ?p' ?rw ?ev ?ps' ?cf ?stx ] |- _ ] =>
    destruct (bundle_asp $p' $rw $ev $ps' $cf $stx) as [bres stb] eqn:Hbun
  end.
  destruct bres as [outev | berr] > [ | inversion Hrun ].
  inversion Hrun; subst.
  eapply wf_Evidence_bundle_asp > [ exact Hwf | exact Hbun ].
Qed.

(* CVM appraisal preserves wf. [invoke_APPR'] receives the *canonical*
   structural type [et] ([invoke_APPR] normalizes before calling) plus the
   original output-accumulator type [eo] over the same raw bits. Canonicity
   makes the stuck shapes (left/right projections, bare UNWRAP) vacuous --
   [et_size_canon] errs on them, contradicting [wf_Evidence] -- so the
   remaining recursion is purely structural. *)
Lemma wf_Evidence_invoke_APPR : forall sc et r eo st e' st',
  normalize_ev (session_context sc) et = et ->
  wf_Evidence (session_context sc) (evc r et) ->
  wf_Evidence (session_context sc) (evc r eo) ->
  invoke_APPR' r et eo sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  intros sc et.
  induction et as [ | nid | p par et' IH | et' IH | et' IH | et1 IHet1 et2 IHet2 ];
  intros r eo st e' st' Hcanon Hwf Hwfo Hrun.
  - (* mt_evt: returns the accumulated output evidence unchanged *)
    cbn [invoke_APPR'] in Hrun.
    cbv beta iota zeta delta [get_config CVM_bind CVM_ret CVM_ask ret] in Hrun.
    inversion Hrun; subst.
    exact Hwfo.
  - (* nonce_evt: one check-nonce ASP over the accumulated output *)
    cbn [invoke_APPR'] in Hrun.
    cbv beta iota zeta delta [get_config CVM_bind CVM_ret CVM_ask ret] in Hrun.
    eapply wf_Evidence_invoke_ASP > [ exact Hwfo | exact Hrun ].
  - (* asp_evt *)
    destruct par as [asp_id args].
    (* size equation for the canonical asp type: prunes no-sig and UNWRAP *)
    pose proof (wf_Evidence_inv _ _ _ Hwf) as Hsz.
    unfold et_size in Hsz.
    rewrite Hcanon in Hsz.
    rewrite et_size_canon_asp_unfold in Hsz.
    destruct ((asp_types (session_context sc)) ![ asp_id ]) as [ [fwd attrs] | ] eqn:Hlk >
    [ | inversion Hsz ].
    destruct fwd as [ [n nlt] | [n nlt] | | [n nlt] isig ].
    + (* REPLACE: appraisal is just the dual ASP *)
      cbn [invoke_APPR'] in Hrun.
      cbv beta iota zeta delta [get_config get_asp_dual get_asp_type hoist_result
        hoist_option CVM_bind CVM_ret CVM_fail CVM_ask ret] in Hrun.
      destruct ((asp_comps (session_context sc)) ![ asp_id ]) as [dual | ] eqn:Hdual >
      [ | inversion Hrun ].
      rewrite Hlk in Hrun.
      cbv beta iota zeta in Hrun.
      eapply wf_Evidence_invoke_ASP > [ exact Hwfo | exact Hrun ].
    + (* WRAP: dual ASP (the unwrapper), runtime size check, then recurse *)
      assert (Hcanon' : normalize_ev (session_context sc) et' = et').
      { eapply canon_asp_inner > [ exact Hcanon | exact Hlk | discriminate ]. }
      cbn [invoke_APPR'] in Hrun.
      cbv beta iota zeta delta [get_config get_asp_dual get_asp_type hoist_result
        hoist_option CVM_bind CVM_ret CVM_fail CVM_ask ret] in Hrun.
      destruct ((asp_comps (session_context sc)) ![ asp_id ]) as [dual | ] eqn:Hdual >
      [ | inversion Hrun ].
      rewrite Hlk in Hrun.
      cbv beta iota zeta in Hrun.
      match! goal with
      | [ _h : context [ invoke_ASP ?ev ?ps' ?cf ?stx ] |- _ ] =>
        destruct (invoke_ASP $ev $ps' $cf $stx) as [ares st1] eqn:HASP
      end.
      destruct ares as [ev1 | aerr] > [ | inversion Hrun ].
      destruct ev1 as [r'' et''].
      pose proof (wf_Evidence_invoke_ASP _ _ _ _ _ _ Hwfo HASP) as Hwf1.
      pose proof (invoke_ASP_evidence _ _ _ _ _ _ HASP) as Hshape.
      cbv beta iota zeta delta [get_et] in Hshape.
      subst et''.
      pose proof (wf_Evidence_inv _ _ _ Hwf1) as Hlen1.
      destruct (et_size (session_context sc)
                  (asp_evt (session_plc sc) (asp_paramsC dual args) eo))
        as [n1 | ] eqn:Hsz1 > [ | inversion Hrun ].
      destruct (et_size (session_context sc) et') as [n2 | ] eqn:Hsz2 >
      [ | inversion Hrun ].
      destruct (DecEq.dec_eq n1 n2) as [Heqn | Hneq] > [ | inversion Hrun ].
      inversion Hlen1; subst.
      eapply IH > [ exact Hcanon' | | exact Hwf1 | exact Hrun ].
      econstructor.
      * reflexivity.
      * rewrite Hsz2; f_equal; lia.
    + (* UNWRAP: vacuous -- a canonical UNWRAP-headed asp has no size *)
      inversion Hsz.
    + (* EXTEND: peel the extension, dual ASP on it, recurse on the rest *)
      assert (Hcanon' : normalize_ev (session_context sc) et' = et').
      { eapply canon_asp_inner > [ exact Hcanon | exact Hlk | discriminate ]. }
      destruct (et_size_canon (session_context sc) et') as [nin | ] eqn:Hszin >
      [ | cbv beta iota zeta delta [bind] in Hsz; inversion Hsz ].
      cbv beta iota zeta delta [bind] in Hsz.
      assert (Hszet' : et_size (session_context sc) et' = res nin).
      { unfold et_size. rewrite Hcanon'. exact Hszin. }
      assert (Hlen_r : n + nin = List.length r).
      { inversion Hsz. reflexivity. }
      cbn [invoke_APPR'] in Hrun.
      cbv beta iota zeta delta [get_config get_asp_dual get_asp_type hoist_result
        hoist_option split_ev inc_id add_trace get_trace get_evid get_st
        put_trace get_pl CVM_bind CVM_ret CVM_fail CVM_ask CVM_put CVM_get
        ret] in Hrun.
      destruct ((asp_comps (session_context sc)) ![ asp_id ]) as [dual | ] eqn:Hdual >
      [ | inversion Hrun ].
      rewrite Hlk in Hrun.
      cbv beta iota zeta in Hrun.
      destruct (peel_n_rawev n r) as [ [ls1 r_ev] | ] eqn:Hpeel > [ | inversion Hrun ].
      pose proof (peel_n_rawev_result_spec _ _ _ _ Hpeel) as Hps.
      destruct Hps as [Hreq Hlenls1].
      match! goal with
      | [ _h : context [ invoke_ASP ?ev ?ps' ?cf ?stx ] |- _ ] =>
        destruct (invoke_ASP $ev $ps' $cf $stx) as [ares st1] eqn:HASP
      end.
      destruct ares as [ev1 | aerr] > [ | inversion Hrun ].
      pose proof (wf_Evidence_invoke_ASP _ _ _ _ _ _ Hwfo HASP) as Hwf1.
      assert (Hwf2 : wf_Evidence (session_context sc) (evc r_ev et')).
      { econstructor.
        - reflexivity.
        - rewrite Hszet'.
          f_equal.
          subst r.
          rewrite length_app in Hlen_r.
          lia. }
      match! goal with
      | [ _h : context [ invoke_APPR' ?rr ?ett ?eoo ?cf ?stx ] |- _ ] =>
        destruct (invoke_APPR' $rr $ett $eoo $cf $stx) as [ares2 st2] eqn:Hrec
      end.
      destruct ares2 as [ev2 | rerr] > [ | inversion Hrun ].
      pose proof (IH _ _ _ _ _ Hcanon' Hwf2 Hwf2 Hrec) as Hwfev2.
      destruct ev1 as [b1 t1].
      destruct ev2 as [b2 t2].
      cbv beta iota zeta delta [join_seq get_pl get_config inc_id add_trace
        get_trace get_evid get_st put_trace CVM_bind CVM_ret CVM_ask CVM_put
        CVM_get ret] in Hrun.
      inversion Hrun; subst.
      eapply wf_Evidence_split > [ exact Hwf1 | exact Hwfev2 ].
  - (* left_evt: vacuous -- a canonical projection is stuck, so it has no size *)
    pose proof (wf_Evidence_inv _ _ _ Hwf) as Hsz.
    unfold et_size in Hsz.
    rewrite Hcanon in Hsz.
    cbv beta iota delta [et_size_canon] in Hsz.
    inversion Hsz.
  - (* right_evt: vacuous, as for left_evt *)
    pose proof (wf_Evidence_inv _ _ _ Hwf) as Hsz.
    unfold et_size in Hsz.
    rewrite Hcanon in Hsz.
    cbv beta iota delta [et_size_canon] in Hsz.
    inversion Hsz.
  - (* split_evt: peel both halves, recurse on each against the projected
       output accumulator, rejoin *)
    pose proof (canon_split _ _ _ _ Hcanon) as Hc.
    destruct Hc as [Hc1 Hc2].
    cbn [invoke_APPR'] in Hrun.
    cbv beta iota zeta delta [get_config hoist_result split_ev inc_id add_trace
      get_trace get_evid get_st put_trace get_pl CVM_bind CVM_ret CVM_fail
      CVM_ask CVM_put CVM_get ret] in Hrun.
    destruct (et_size (session_context sc) et1) as [n1 | ] eqn:Hs1 > [ | inversion Hrun ].
    destruct (et_size (session_context sc) et2) as [n2 | ] eqn:Hs2 > [ | inversion Hrun ].
    destruct (peel_n_rawev n1 r) as [ [ev_l r_ev] | ] eqn:Hp1 > [ | inversion Hrun ].
    destruct (peel_n_rawev n2 r_ev) as [ [ev_r rest] | ] eqn:Hp2 > [ | inversion Hrun ].
    pose proof (peel_n_rawev_result_spec _ _ _ _ Hp1) as Hps1.
    destruct Hps1 as [Hreq1 Hlen_l].
    pose proof (peel_n_rawev_result_spec _ _ _ _ Hp2) as Hps2.
    destruct Hps2 as [Hreq2 Hlen_r].
    destruct rest as [ | junk rest' ] > [ | inversion Hrun ].
    rewrite app_nil_r in Hreq2.
    subst r_ev.
    destruct (equiv_EvidenceT (session_context sc) et1 (left_evt eo)) eqn:Hq1 >
    [ | inversion Hrun ].
    destruct (equiv_EvidenceT (session_context sc) et2 (right_evt eo)) eqn:Hq2 >
    [ | inversion Hrun ].
    cbv beta iota zeta in Hrun.
    assert (Hwfl : wf_Evidence (session_context sc) (evc ev_l et1)).
    { econstructor > [ exact Hlen_l | exact Hs1 ]. }
    assert (Hwflo : wf_Evidence (session_context sc) (evc ev_l (left_evt eo))).
    { econstructor > [ exact Hlen_l | ].
      pose proof (equiv_EvidenceT_impl_et_size_same _ _ _ Hq1) as Hq1'.
      rewrite <- Hq1'.
      exact Hs1. }
    assert (Hwfr : wf_Evidence (session_context sc) (evc ev_r et2)).
    { econstructor > [ exact Hlen_r | exact Hs2 ]. }
    assert (Hwfro : wf_Evidence (session_context sc) (evc ev_r (right_evt eo))).
    { econstructor > [ exact Hlen_r | ].
      pose proof (equiv_EvidenceT_impl_et_size_same _ _ _ Hq2) as Hq2'.
      rewrite <- Hq2'.
      exact Hs2. }
    match! goal with
    | [ _h : context [ invoke_APPR' ?rr ?ett ?eoo ?cf ?stx ] |- _ ] =>
      destruct (invoke_APPR' $rr $ett $eoo $cf $stx) as [ares1 st1] eqn:Hr1
    end.
    destruct ares1 as [ev1 | rerr] > [ | inversion Hrun ].
    pose proof (IHet1 _ _ _ _ _ Hc1 Hwfl Hwflo Hr1) as Hwfev1.
    match! goal with
    | [ _h : context [ invoke_APPR' ?rr ?ett ?eoo ?cf ?stx ] |- _ ] =>
      destruct (invoke_APPR' $rr $ett $eoo $cf $stx) as [ares2 st2] eqn:Hr2
    end.
    destruct ares2 as [ev2 | rerr2] > [ | inversion Hrun ].
    pose proof (IHet2 _ _ _ _ _ Hc2 Hwfr Hwfro Hr2) as Hwfev2.
    destruct ev1 as [b1 t1].
    destruct ev2 as [b2 t2].
    cbv beta iota zeta delta [join_seq get_pl get_config inc_id add_trace
      get_trace get_evid get_st put_trace CVM_bind CVM_ret CVM_ask CVM_put
      CVM_get ret] in Hrun.
    inversion Hrun; subst.
    eapply wf_Evidence_split > [ exact Hwfev1 | exact Hwfev2 ].
Qed.

Lemma wf_Evidence_proc_left : forall G e ep,
  wf_Evidence G e ->
  wf_Evidence G (proc_ev_path_left_ev ep e).
Proof.
  destruct ep; ff; eapply wf_Evidence_mt_evc.
Qed.

Lemma wf_Evidence_proc_right : forall G e ep,
  wf_Evidence G e ->
  wf_Evidence G (proc_ev_path_right_ev ep e).
Proof.
  destruct ep; ff; eapply wf_Evidence_mt_evc.
Qed.

(** * Theorem:  CVM execution preserves well-formedness of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Theorem cvm_preserves_wf_Evidence : forall t st st' e e' sc,
  wf_Evidence (session_context sc) e ->
  build_cvm e t sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  induction t; simpl in *; intros; cvm_monad_unfold.
  - ff;
    try (match! goal with
    | [ |- wf_Evidence _ mt_evc ] => eapply wf_Evidence_mt_evc
    | [ h : Nat.eqb _ _ = true |- _ ] =>
      rewrite PeanoNat.Nat.eqb_eq in $h
    end);
    try (econstructor; simpl in *; ff; fail);
    try (invc H;
      econstructor; ff;
      repeat find_rewrite;
      repeat find_injection;
      ff with u;
      repeat (rewrite length_app in *);
      f_equal; lia).
    (* APPR: [invoke_APPR] hands [invoke_APPR'] the *normalized* structural
       type, so the canonicity premise is idempotence and the structural wf
       premise follows by normalize-invariance of [et_size]. *)
    (* residual [bundle_asp] outputs: each kind's runtime length check is
       exactly the [et_size] equation wf needs *)
    all: try (econstructor >
      [ reflexivity
      | erewrite et_size_asp_replace > [ reflexivity | eassumption ] ]; fail).
    all: try (econstructor >
      [ reflexivity
      | erewrite et_size_asp_wrap > [ reflexivity | eassumption ] ]; fail).
    all: try (econstructor > [ reflexivity | eassumption ]; fail).
    all: try (eapply wf_Evidence_inv in H; econstructor >
      [ rewrite length_app; reflexivity
      | erewrite et_size_asp_extend > [ rewrite H; reflexivity | eassumption ] ];
      fail).
    (* APPR: [invoke_APPR] hands [invoke_APPR'] the *normalized* structural
       type, so the canonicity premise is idempotence and the structural wf
       premise follows by normalize-invariance of [et_size]. *)
    eapply wf_Evidence_invoke_APPR >
    [ eapply normalize_ev_idempotent
    | eapply wf_Evidence_normalize_ev; eassumption
    | eassumption
    | eassumption ].
  - ff;
    find_eapply_lem_hyp do_remote_res_axiom; eauto; ff.
    Unshelve. 
    eapply 0.
  - ff.
  - ff; simpl in *.
    eapply IHt1 in Heq > [ | eapply wf_Evidence_proc_left; ff ].
    eapply IHt2 in Heq0 > [ | eapply wf_Evidence_proc_right; ff ].
    ff; eauto with wf_Evidence.
  - ff; simpl in *.
    find_eapply_lem_hyp parallel_vm_thread_axiom; ff.
    eapply IHt1 in Heq > [ | eapply wf_Evidence_proc_left; ff ].
    destruct e;
    ff; eauto with wf_Evidence.

    eapply IHt2 in Hex;
    ff; eauto with wf_Evidence.
    eapply wf_Evidence_mt_evc.
Qed.

Theorem invoke_APPR_respects_events : forall G et r eo st sc st' e' i m evs,
  G = session_context sc ->
  well_formed_context (session_context sc) ->
  st_evid st = i ->
  st_trace st = m ->
  invoke_APPR' r et eo sc st = (res e', st') ->
  appr_events' (session_context sc) (session_plc sc) et eo i = res evs ->
  st_trace st' = m ++ evs.
Proof.
  intros G.
  induction et;
  simpl in *; intros; cvm_monad_unfold.
  - ff; rewrite app_nil_r; ff.
  - ff.
  - ff with u;
    repeat (find_eapply_lem_hyp peel_n_rawev_result_spec); ff;
    try (match! goal with
    | [ h : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : appr_events' _ _ ?_e _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2 := Control.hyp h2 in
      eapply invoke_APPR'_spans in $h as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply $ih in $h > [ | | | | | eapply $h2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end;
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat (rewrite <- app_assoc); ff).
  - ff.
  - ff.
  - ff with u;
    repeat (match! goal with
    | [ h : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : appr_events' _ _ ?_e _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2 := Control.hyp h2 in
      eapply invoke_APPR'_spans in $h as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply $ih in $h > [ | | | | | eapply $h2 ]; 
      simpl in *; try reflexivity; ff with l
    end);
    repeat (rewrite <- app_assoc); ff with l.
Qed.

(** * Main Theorem: CVM traces are respected the reference "events"
      semantics. *)
Theorem cvm_trace_respects_events : forall t st m st' i p e evs sc e',
  well_formed_context (session_context sc) ->
  events (session_context sc) (cop_phrase p (get_et e) t) i evs ->
  st_trace st = m ->
  st_evid st = i ->
  session_plc sc = p ->
  build_cvm e t sc st = (res e', st') ->
  st_trace st' = m ++ evs.
Proof.
  induction t; simpl in *; intros.
  - invc H0; simpl in *; cvm_monad_unfold; ff;
    simpl in *;
    repeat (match! goal with
    | [ st : cvm_st |- _ ] => 
      let st := Control.hyp st in
      destruct $st; simpl in *; ff
    | [ e : Evidence |- _ ] => 
      let e := Control.hyp e in
      destruct $e; simpl in *; ff
    end);
    try (match! goal with
    | [ e : EvidenceT |- _ ] => 
      let e := Control.hyp e in
      induction $e; simpl in *; ff with a; fail
    end).
    eapply invoke_APPR_respects_events in H4; ff.
  - ff; invc H0; cvm_monad_unfold; ff;
    find_eapply_lem_hyp events_events_fix_eq;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff;
    assert (List.length rem_evs = n) by (
      find_eapply_lem_hyp events_fix_range;
      eapply events_size_plc_irrel; eauto);
    ff;
    repeat (rewrite <- app_assoc); eauto.
    find_eapply_lem_hyp do_remote_res_axiom; ff.
    find_eapply_lem_hyp cvm_evidence_type; ff.
    Unshelve. eapply 0.

  - ff; cvm_monad_unfold; ff.
    match! goal with
    | [ h : events _ _ _ _ |- _ ] => 
      invc $h; ff
    end; cvm_monad_unfold; ff;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heq as ?; eauto;
    eapply cvm_evidence_type in Heq as ?; ff.
    rewrite app_assoc. 
    rewrite <- H0.
    eapply IHt2 in H4; ff.
    eapply cvm_spans; ff;
    eapply events_range; eauto.
  - destruct e; Control.enter (fun () => ff with a;
    match! goal with
    | [ h : events _ _ _ _ |- _ ] => 
      invc $h; ff
    end; cvm_monad_unfold; ff;
    cvm_monad_unfold; ff with a;
    eapply IHt1 in Heq as ?; eauto;
    try (destruct s, s, s0; ff; fail);
    eapply cvm_spans in Heq as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      eapply events_range; eauto; ff; fail); 
    ff;
    eapply IHt2 in Heq0 as ? > [ | | | | | ]; ff;
    repeat (erewrite <- app_assoc); ff;
    find_eapply_lem_hyp cvm_spans; ff;
    eapply events_range; eauto; ff with a).
  - destruct e; Control.enter (fun () =>
    ff with a; invc H0; ff with a;
    cvm_monad_unfold; ff with a;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff;
    eapply IHt1 in Heq as ?; eauto; ff; try lia;
    eapply cvm_spans in Heq as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite; try lia;
    repeat (rewrite <- app_assoc); simpl in *; ff;
    repeat find_rewrite; repeat find_injection; eauto;
    assert (st_evid st + 2 + List.length evs1 = st_evid st + 1 + 1 + List.length evs1) by lia;
    ff;
    erewrite events_events_fix_eq in *; ff;
    assert (n = List.length evs2) by (
      repeat (find_eapply_lem_hyp events_fix_range); eauto; ff);
    ff).
Qed.

Corollary cvm_trace_respects_events_default : forall G,
  well_formed_context G ->
  forall t st st' i p e evs sc e',
  st_trace st = nil ->
  st_evid st = i ->
  session_plc sc = p ->
  session_context sc = G ->
  events G (cop_phrase p (get_et e) t) i evs ->

  build_cvm e t sc st = (res e', st') ->
  st_trace st' = evs.
Proof.
  intros.
  eapply cvm_trace_respects_events in H5; eauto;
  simpl in *; ff.
Qed.
