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
From CoplandSpec Require Import Term_Defs Event_System.
From CVM Require Import Impl St Attestation_Session Monad Cvm_Axioms.
Local Open Scope list_scope.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2,
  peel_n_rawev n ls = res (ls1, ls2) ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; ff u, a.
Qed.

Lemma peel_n_none_spec : forall n ls e,
  peel_n_rawev n ls = err e ->
  length ls < n.
Proof.
  induction n; ff u, a, l.
Qed.

Lemma invoke_APPR_deterministic : forall G e sc st1 st2 st1' st2' res1 res2 r oe,
  G = session_context sc ->
  st_evid st1 = st_evid st2 ->
  invoke_APPR' r e oe sc st1 = (res1, st1') ->
  invoke_APPR' r e oe sc st2 = (res2, st2') ->
  res1 = res2 /\ st_evid st1' = st_evid st2'.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  simpl in *; intros;
  try (ux cvm (); intuition; repeat find_injection; eauto; fail).
  - ff (ux cvm).
  - ux cvm ();
    target_break_match H3; ff;
    try (Control.enter (fun () =>
    match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      (* let h1 := Control.hyp h1 in *)
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end)).
  - cvm_monad_unfold;
    target_break_match H3;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto.
    ateb_unpack H9; ff a.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    unpack_atebs; ff a.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto; unpack_atebs; ff a.
  - cvm_monad_unfold;
    target_break_match H1;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H2);
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
  induction et using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; subst; cvm_monad_unfold.
  - ff.
  - target_break_match H0.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H3);
    Control.enter (fun () =>
    match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end).
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H3).
    unpack_atebs; ff a.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H3);
    Control.enter (fun () =>
    match! goal with
    | [ h1 : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : invoke_APPR' _ ?_e _ _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let h2 := Control.hyp h2 in
      let ih := Control.hyp ih in
      eapply $ih in $h1; try (eapply $h2); ff
    end).
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H3);
    unpack_atebs; ff a.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H3);
    unpack_atebs; ff a.
  - target_break_match H0;
    repeat find_injection;
    repeat find_rewrite;
    subst; try (simple congruence 3);
    eauto;
    try (target_break_match H1);
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
  induction t; simpl in *; cvm_monad_unfold; ff;
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
  solve [ eapply invoke_APPR_deterministic; ff ].
Qed.

Lemma appr_events'_errs_deterministic : forall G p e e' i1 e1,
  appr_events' G p e e' i1 = err e1 ->
  forall i2, appr_events' G p e e' i2 = err e1.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; ff u, a;
  try (find_eapply_lem_hyp IHe; ff; fail);
  try (find_eapply_lem_hyp IHe1; ff);
  try (find_eapply_lem_hyp IHe2; ff);
  try (ateb_errs_same; eauto; fail);
  try (ateb_diff);
  try (ateb_same); ff a.
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
  induction t; ff u, a;
  eapply asp_events_errs_deterministic; eauto.
Qed.

Lemma events_fix_only_one_error : forall G t p e i1 i2 e1 e2,
  events_fix G p e t i1 = err e1 ->
  events_fix G p e t i2 = err e2 ->
  e1 = e2.
Proof.
  induction t; ff u, a;
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
  - ff; simpl in *; 
    repeat (match! goal with
    | [ h : parallel_vm_thread _ _ _ _ = ?_res |- _ ] =>
      eapply parallel_vm_thread_axiom in $h;
      try reflexivity; break_exists
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
    end).
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
  induction et using (Evidence_subterm_path_Ind_special G');
  ff u, (ux cvm), a;
  repeat (match! goal with
  | [ h : invoke_APPR' _ ?_e _ _ _ = _,
      ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
    let ih := Control.hyp ih in
    eapply $ih in $h; ff l;
    try lia
  end); try (ateb_same); ff a.
Qed.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
| et_same_asps_mt : et_same_asps mt_evt mt_evt
| et_same_asps_nonce : forall n1 n2, et_same_asps (nonce_evt n1) (nonce_evt n2)
| et_same_asps_asp : forall p1 p2 e1 e2 aid args1 args2 targp1 targp2 targ1 targ2,
    et_same_asps e1 e2 ->
    et_same_asps 
      (asp_evt p1 (asp_paramsC aid args1 targp1 targ1) e1) 
      (asp_evt p2 (asp_paramsC aid args2 targp2 targ2) e2)
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

Lemma et_same_asps_symm : forall e1 e2,
  et_same_asps e1 e2 -> et_same_asps e2 e1.
Proof.
  intros.
  prep_induction H.
  induction H; eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_symm : et_same_asps_db.

Lemma ev_subterm_path_et_same_asps : forall G e1 e2 e1' e2' l,
  et_same_asps e1 e2 ->
  Evidence_Subterm_path G e1' l e1 ->
  Evidence_Subterm_path G e2' l e2 ->
  et_same_asps e1' e2'.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl in *;
  try (invc H0; invc H1; eauto using et_same_asps; fail).
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H1; invc H2; try congruence; eauto using et_same_asps.
Qed.
Local Hint Resolve ev_subterm_path_et_same_asps : et_same_asps_db.

Lemma et_same_asps_ateb_errs_det : forall {A} G (f : _ -> A) e1 e2 l r1 r2,
  et_same_asps e1 e2 ->
  apply_to_evidence_below G f l e1 = err r1 ->
  apply_to_evidence_below G f l e2 = err r2 ->
  r1 = r2.
Proof.
  induction e1; simpl in *; ff;
  try (invc H; simpl in *; ff; fail).
Qed.

Lemma et_same_asps_ateb_errs_only : forall {A} G (f : _ -> A) e1 e2 l r1 r2,
  et_same_asps e1 e2 ->
  apply_to_evidence_below G f l e1 = err r1 ->
  apply_to_evidence_below G f l e2 = res r2 ->
  False.
Proof.
  induction e1; simpl in *; ff;
  try (invc H; simpl in *; ff; fail).
Qed.

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros G.
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; ff; eauto;
  try (invc H; ff u, a; fail);
  try (invc H1; ff u, a; fail).
  - invc H1; ff u, a.
    * unpack_atebs; ff a; eapply H0; ff a;
      eapply ev_subterm_path_et_same_asps; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr; ff a; 
      eauto with et_same_asps_db.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff a; 
      eauto with et_same_asps_db.
    * f_equal; eapply et_same_asps_ateb_errs_det; ff a.
  - invc H0; ff u, a.
  - invc H0; ff u, a.
    * unpack_atebs; ff a; eapply H; ff a;
      eapply ev_subterm_path_et_same_asps; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr; ff a; 
      eauto with et_same_asps_db.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff a; 
      eauto with et_same_asps_db.
    * f_equal; eapply et_same_asps_ateb_errs_det; ff a.
  - invc H0; ff u, a.
    * unpack_atebs; ff a; eapply H; ff a;
      eapply ev_subterm_path_et_same_asps; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr; ff a; 
      eauto with et_same_asps_db.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff a; 
      eauto with et_same_asps_db.
    * f_equal; eapply et_same_asps_ateb_errs_det; ff a.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : et_same_asps_db.

Lemma et_same_asps_asp_dir : forall e1 e2 asp_id args1 args2 targ_plc1 targ_plc2 targ1 targ2 p1 p2 par1 par2,
  et_same_asps e1 e2 ->
  par1 = (asp_paramsC asp_id args1 targ_plc1 targ1) ->
  par2 = (asp_paramsC asp_id args2 targ_plc2 targ2) ->
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
  unfold equiv_EvidenceT in *; ff u, a.
Qed.

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2 e1o e2o,
  et_same_asps e1 e2 ->
  et_same_asps e1o e2o ->
  appr_procedure' G p1 e1 e1o = res e1' ->
  appr_procedure' G p2 e2 e2o = res e2' ->
  et_same_asps e1' e2'.
Proof.
  intros G.
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; cvm_monad_unfold.
  - invc H; simpl in *; ff; econstructor; eauto.
  - invc H; simpl in *; ff; econstructor; eauto.
  - inv H1; simpl in *; ff.
    * econstructor; eauto.
    * eapply IHe1 in H4; ff; econstructor; eauto.
    * ff u, a.
      econstructor; eauto.
      econstructor; eauto.
  - inv H1; simpl in *; ff u, a;
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H0 in Hf0; try (eapply Hf); ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H1; simpl in *; ff.
  - inv H0; simpl in *; ff u, a.
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H in Hf0; try (eapply Hf); ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H0; simpl in *; ff u, a;
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H in Hf0; try (eapply Hf); ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H; simpl in *; ff u, a;
    eapply IHe1_1 in Heqr; try (eapply Heqr1); eauto;
    try (econstructor; eauto; fail).
    eapply IHe1_2 in Heqr0; try (eapply Heqr2); eauto;
    try (econstructor; eauto; fail).
Qed.
Local Hint Resolve et_same_asps_appr_procedure : et_same_asps_db.

Lemma et_same_asps_eval_same_asps : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = res e1' ->
  eval G p2 e2 t = res e2' ->
  et_same_asps e1' e2'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; ff; eauto using et_same_asps.
    eapply et_same_asps_appr_procedure; eauto.
  - ff u, a.
  - ff u, a.
    repeat (match! goal with
    | [ h1 : eval _ ?_p1 ?_e1 ?_t = res ?_e1',
        h2 : eval _ ?_p2 ?_e2 ?_t = res ?_e2',
        ih : context[eval _ _ _ ?_t = _ -> _] |- _ ] =>
      let h1v := Control.hyp h1 in
      let ih := Control.hyp ih in
      eapply $ih in $h2; try (eapply $h1v); 
      clear $h1
    end);
    try (econstructor; eauto; fail);
    destruct s, s, s0; simpl in *; eauto;
    econstructor.
  - ff u, a.
    repeat (match! goal with
    | [ h1 : eval _ ?_p1 ?_e1 ?_t = res ?_e1',
        h2 : eval _ ?_p2 ?_e2 ?_t = res ?_e2',
        ih : context[eval _ _ _ ?_t = _ -> _] |- _ ] =>
      let h1v := Control.hyp h1 in
      let ih := Control.hyp ih in
      eapply $ih in $h2; try (eapply $h1v); 
      clear $h1
    end);
    try (econstructor; eauto; fail);
    destruct s, s, s0; simpl in *; eauto;
    econstructor.
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
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; ff u, a;
  try (invc H; ff; fail);
  try (invc H1; ff u, a; fail).
  - invc H1; ff u, a.
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H0; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H0; ff u, a.
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H0; ff u, a.
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H; simpl in *; ff u, a.
    eapply IHe1_1 in Heqr1; try reflexivity; subst; ff.
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
  induction t; simpl in *; intuition; ff u, a;
  eauto with et_same_asps_db.
  - eapply et_same_asps_impl_appr_events_size_same; eauto.
  - destruct s, s, s0; simpl in *; ff u, a;
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
    end).
  - destruct s, s, s0; simpl in *; ff u, a;
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
    end).
Qed.

Lemma events_size_plc_irrel : forall G t et p1 p2 n1 n2,
  events_size G p1 et t = res n1 ->
  events_size G p2 et t = res n2 ->
  n1 = n2.
Proof.
  induction t; simpl in *; intuition; ff u, a;
  repeat (match! goal with
  | [ h1 : events_size _ _ _ ?_t = _,
      h2 : events_size _ _ _ ?_t = _,
      ih : context[events_size _ _ _ ?_t] |- _ ] =>
    let ih := Control.hyp ih in
    let h2v := Control.hyp h2 in
    eapply $ih in $h1 > [ | eapply $h2v ];
    clear $h2; ff
  end); try lia.
  - eapply events_size_eval_res_irrel in Heqr4; ff.
Qed.

Definition well_formed_context (G : GlobalContext) : Prop :=
  (asp_types G) ![ sig_aspid ] = Some (ev_arrow EXTEND InAll (OutN 1)) /\
  (asp_types G) ![ hsh_aspid ] = Some (ev_arrow REPLACE InAll (OutN 1)) /\
  (asp_types G) ![ enc_aspid ] = Some (ev_arrow WRAP InAll (OutN 1)) /\
  (asp_types G) ![ check_nonce_aspid ] = Some (ev_arrow EXTEND InAll (OutN 1)).

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
  induction et using (Evidence_subterm_path_Ind_special G);
  intuition; simpl in *.
  - simpl in *; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u, a.
    cvm_monad_unfold; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u;
    cvm_monad_unfold; ff u.
    * ateb_same; find_eapply_lem_hyp H0; ff; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u;
    cvm_monad_unfold; ff u.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u;
    cvm_monad_unfold; ff u;
    ateb_same; find_eapply_lem_hyp H; ff; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u;
    cvm_monad_unfold; ff u;
    ateb_same; find_eapply_lem_hyp H; ff; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff u;
    cvm_monad_unfold; ff u, a.
    
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
    erewrite H1 in *; ff.
  - ff u, a; cvm_monad_unfold; ff;
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
  - ff u, a; cvm_monad_unfold; ff;
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply IHt2 in Heqp0 as ?; simpl in *;
    ff; find_higher_order_rewrite; eauto.
  - ff u, a; cvm_monad_unfold; ff;
    destruct s, s, s0; ff u, a;
    find_eapply_lem_hyp parallel_vm_thread_axiom; eauto; ff u, a;
    try (unfold mt_evc in *; ff);
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
  - cvm_monad_unfold; ff u; 
    find_eapply_lem_hyp events_size_plc_irrel;
    try (eapply Heqr0); ff l.
  - cvm_monad_unfold; ff u.

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
    destruct e; simpl in *; ff.
    eapply IHt2 in H0 as ? > [ | | eapply Heqr1]; ff l.
  - cvm_monad_unfold; ff u, a.
    eapply IHt1 in Heqp > [ | eauto | destruct s, s, s0; ff ]; ff.
    eapply IHt2 in Heqp0 > [ | eauto | destruct s, s, s0; ff ]; ff.
    lia.
  - ff u, a; cvm_monad_unfold; ff;
    repeat find_rewrite;
    eapply IHt1 in Heqp; try (eapply Heqr);
    simpl in *; eauto; ff;
    destruct s, s, s0; simpl in *; ff; try lia;
    repeat find_rewrite; repeat find_injection; try lia;
    unfold mt_evc in *; ff l.
Qed.

Lemma wf_Evidence_split_l : forall G e s,
  wf_Evidence G e ->
  wf_Evidence G (splitEv_l s e).
Proof.
  intros; invc H;
  unfold splitEv_l; ff;
  econstructor; simpl in *; auto.
  Unshelve. eapply 0.
Qed.
Local Hint Resolve wf_Evidence_split_l : wf_Evidence.

Lemma wf_Evidence_split_r : forall G e s,
  wf_Evidence G e ->
  wf_Evidence G (splitEv_r s e).
Proof.
  intros; invc H;
  unfold splitEv_r; ff;
  econstructor; simpl in *; auto.
  Unshelve. eapply 0.
Qed.
Local Hint Resolve wf_Evidence_split_r : wf_Evidence.

Lemma wf_Evidence_split : forall G r1 r2 et1 et2,
  wf_Evidence G (evc r1 et1) ->
  wf_Evidence G (evc r2 et2) ->
  wf_Evidence G (evc (r1 ++ r2) (split_evt et1 et2)).
Proof.
  intros; invc H; invc H0; econstructor; ff;
  rewrite length_app; ff.
Qed.
Local Hint Resolve wf_Evidence_split : wf_Evidence.

Lemma wf_Evidence_impl_et_size_res : forall G e,
  wf_Evidence G e ->
  exists n, et_size G (get_et e) = res n.
Proof.
  destruct e; 
  induction e; simpl in *; intros;
  invc H; simpl in *; eauto.
Qed.

Lemma wf_Evidence_mt_evc : forall G,
  wf_Evidence G mt_evc.
Proof.
  unfold mt_evc; econstructor; simpl in *; eauto.
  Unshelve. eapply 0.
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
  intros G; induction e using (Evidence_subterm_path_Ind_special G); ff;
  try (exists (meta_machinery_pad_n n nil); econstructor; eauto;
    ff u;
    rewrite meta_machinery_pad_n_size; ff; fail).
  - eexists; eapply wf_Evidence_mt_evc. 
  - exists [passed_bs]; econstructor; eauto.
Qed.

Lemma wf_Evidence_asp_unfold_more : forall G r p e n a a1 p0 t,
  wf_Evidence G (evc r (asp_evt p (asp_paramsC a a1 p0 t) e)) ->
  et_size G e = res n ->
  forall sig n',
  (asp_types G) ![ a ] = Some (ev_arrow EXTEND sig (OutN n')) ->
  et_size G (asp_evt p (asp_paramsC a a1 p0 t) e) = res (n' + n).
Proof.
  intros.
  prep_induction H.
  induction H; ff u.
Qed.

Lemma wf_Evidence_split_unfold : forall G r e1 e2,
  wf_Evidence G (evc r (split_evt e1 e2)) ->
  (exists r1, wf_Evidence G (evc r1 e1)) /\ (exists r2, wf_Evidence G (evc r2 e2)).
Proof.
  intros.
  prep_induction H;
  induction H; ff u; 
  split; eapply wf_Evidence_exists; ff.
Qed.

Lemma wf_Evidence_asp_unpack : forall G r p e a0 a1 p0 t,
  wf_Evidence G (evc r (asp_evt p (asp_paramsC a0 a1 p0 t) e)) ->
  forall in_sig n n',
  (asp_types G) ![ a0 ] = Some (ev_arrow EXTEND in_sig (OutN n)) ->
  et_size G e = res n' ->
  List.length r = n + n'.
Proof.
  intros.
  prep_induction H; ff; invc H; ff.
Qed.

Lemma wf_Evidence_invoke_APPR : forall G et r eo st e' st' sc,
  G = session_context sc ->
  wf_Evidence (session_context sc) (evc r et) ->
  wf_Evidence (session_context sc) (evc r eo) ->
  invoke_APPR' r et eo sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G); intuition.
  - ff; cvm_monad_unfold; ff; eapply wf_Evidence_mt_evc.
  - ff; cvm_monad_unfold; ff;
    repeat (match! goal with
    | [ h : wf_Evidence _ _ |- _ ] => 
      invc $h; ff
    end); try (econstructor; ff; repeat (rewrite length_app); ff u;
    try (ateb_diff); fail).

  - simpl in *; ff u; cvm_monad_unfold; ff.
    all: try (ff u;
      repeat (match! goal with
      | [ h : wf_Evidence _ _ |- _ ] => invc $h; ff
      end);
      ff u;
      try (find_eapply_lem_hyp peel_n_rawev_result_spec; ff u);
      try (match! goal with
      | [ h : invoke_APPR' _ ?_t _ _ _ = _, 
          ih : context[invoke_APPR' _ ?_t _ _ _ = _ -> _] |- _ ] =>
        let ihv := Control.hyp ih in
        eapply $ihv in $h > [ eauto | reflexivity | | ]; clear $ih
      end);
      econstructor; repeat (match! goal with
      | [ h : wf_Evidence _ _ |- _ ] => invc $h; ff u
      end);
      repeat (rewrite length_app in *); ff u, l; try (f_equal); lia).
  - repeat (cvm_monad_unfold; ff).
    ateb_unpack Heqr0; ff a.
    eapply H0 in H4; ff.
    invc H2; simpl in *; u (); ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp;
    try (eapply Hesp0); subst.
    econstructor; ff.
  - repeat (cvm_monad_unfold; ff).
  - repeat (cvm_monad_unfold; ff).
    ateb_unpack Heqr0; ff a;
    eapply H in H3; ff.
    invc H1; simpl in *; u (); ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp;
    try (eapply Hesp0); subst.
    econstructor; ff.
  - repeat (cvm_monad_unfold; ff);
    ateb_unpack Heqr0; ff a.
    eapply H in H3; ff.
    invc H1; simpl in *; u (); ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp;
    try (eapply Hesp0); subst.
    econstructor; ff.
  - simpl in *; ff; cvm_monad_unfold; ff.
    repeat (find_eapply_lem_hyp peel_n_rawev_result_spec); ff;
    repeat (rewrite app_nil_r in *); ff.
    eapply IHet1 in Heqp3; try reflexivity.
    * eapply IHet2 in Heqp4; try reflexivity;
      econstructor; repeat (rewrite length_app in *); ff;
      u (); ff;
      repeat (match! goal with
      | [ h : wf_Evidence _ _ |- _ ] => invc $h; ff
      end); ff u;
      repeat (rewrite length_app in *); ff;
      repeat (find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same); ff.
    * econstructor; repeat (rewrite length_app in *); ff u;
      repeat (match! goal with
      | [ h : wf_Evidence _ _ |- _ ] => invc $h; ff
      end); ff u;
      repeat (rewrite length_app in *); ff;
      repeat (find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same); ff.
    * econstructor; repeat (rewrite length_app in *); ff u;
      repeat (match! goal with
      | [ h : wf_Evidence _ _ |- _ ] => invc $h; ff
      end); ff u;
      repeat (rewrite length_app in *); ff;
      repeat (find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same); ff.
Qed.

(** * Theorem:  CVM execution preserves well-formedness of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Theorem cvm_preserves_wf_Evidence : forall t st st' e e' sc,
  wf_Evidence (session_context sc) e ->
  build_cvm e t sc st = (res e', st') ->
  wf_Evidence (session_context sc) e'.
Proof.
  induction t; simpl in *; intuition;
  cvm_monad_unfold; try (ff a; fail).
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
      ff u;
      repeat (rewrite length_app in *);
      f_equal; lia).
    eapply wf_Evidence_invoke_APPR; eauto; destruct e; ff.
  - ff;
    find_eapply_lem_hyp do_remote_res_axiom; eauto; ff.
    Unshelve. 
    ref (Build_Session_Config "" (Build_GlobalContext _ [] []) (fun _ _ => res []) [] [] []).
    eapply 0.
  - ff; simpl in *.
    eapply IHt1 in Heqp; ff; eauto with wf_Evidence.
  - ff; simpl in *.
    find_eapply_lem_hyp parallel_vm_thread_axiom; ff.
    eapply IHt1 in Heqp; ff; eauto with wf_Evidence.
    eapply IHt2 in H0; ff; eauto with wf_Evidence.
    destruct s, s, s0; ff; 
    unfold mt_evc in *; ff;
    eauto with wf_Evidence;
    econstructor; ff l.
    Unshelve.
    eapply 0.
    eapply 0.
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
  induction et using (Evidence_subterm_path_Ind_special G);
  simpl in *; intros; cvm_monad_unfold.
  - ff; rewrite app_nil_r; ff.
  - ff. 
  - ff u;
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
  - ff u;
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
    repeat (rewrite <- app_assoc); ff);
    ateb_same; ff a.
  - ff u;
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
  - ff u;
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
    repeat (rewrite <- app_assoc); ff);
    ateb_same; ff a.
  - ff u;
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
    repeat (rewrite <- app_assoc); ff);
    ateb_same; ff a.
  - ff u;
    repeat (match! goal with
    | [ h : invoke_APPR' _ ?_e _ _ _ = _,
        h2 : appr_events' _ _ ?_e _ _ = _,
        ih : context[invoke_APPR' _ ?_e _ _ _ = _ -> _] |- _ ] =>
      let ih := Control.hyp ih in
      let h2 := Control.hyp h2 in
      eapply invoke_APPR'_spans in $h as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply $ih in $h > [ | | | | | eapply $h2 ]; 
      simpl in *; try reflexivity; ff l
    end);
    repeat (rewrite <- app_assoc); ff l.
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
      induction $e; simpl in *; ff a; fail
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
    repeat (find_higher_order_rewrite); ff.
    Unshelve. eapply 0.

  - ff; cvm_monad_unfold; ff.
    match! goal with
    | [ h : events _ _ _ _ |- _ ] => 
      invc $h; ff
    end; cvm_monad_unfold; ff;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; eauto;
    eapply cvm_evidence_type in Heqp as ?; ff.
    rewrite app_assoc. 
    rewrite <- H0.
    eapply IHt2 in H4; ff.
    eapply cvm_spans; ff;
    eapply events_range; eauto.
  - ff a;
    match! goal with
    | [ h : events _ _ _ _ |- _ ] => 
      invc $h; ff
    end; cvm_monad_unfold; ff;
    cvm_monad_unfold; ff a.
    eapply IHt1 in Heqp as ?; eauto;
    try (destruct s, s, s0; ff; fail);
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail); 
    ff.
    eapply IHt2 in Heqp0 as ? > [ | | destruct s, s, s0; ff | | | ]; ff.
    repeat (erewrite <- app_assoc); ff;
    find_eapply_lem_hyp cvm_spans; ff;
    destruct s, s, s0; ff;
    eapply events_range; eauto; ff a.
  - ff a; invc H0; ff a;
    cvm_monad_unfold; ff a;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; try (destruct s, s, s0; ff; fail); eauto; ff; try lia.
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite; try lia.
    repeat (rewrite <- app_assoc); simpl in *; ff.
    repeat find_rewrite; repeat find_injection; eauto.
    assert (st_evid st + 2 + List.length evs1 = st_evid st + 1 + 1 + List.length evs1) by lia.
    ff.
    erewrite events_events_fix_eq in *; ff.
    assert (n = List.length evs2). {
      repeat (find_eapply_lem_hyp events_fix_range); eauto; ff;
      destruct s, s, s0; ff; unfold mt_evc in *; simpl in *; ff.
    }
    ff.
    destruct s, s, s0; ff; unfold mt_evc in *; simpl in *; ff.
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
