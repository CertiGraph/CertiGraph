Require Import RamifyCoq.lib.List_ext.
Require Import VST.floyd.base.
Require Import VST.floyd.canon.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.

Local Open Scope logic.

Module RAM_FRAME.

Record SingleFrame' l g s: Type := {
  frame: environ -> mpred;
  frame_sound: g |-- l * frame;
  frame_closed: Forall (fun s => closed_wrt_modvars s frame) s
}.

Record SingleFrame: Type := {
  local_assert: environ -> mpred;
  global_assert: environ -> mpred;
  stats: list statement;
  real_frame: SingleFrame' local_assert global_assert stats
}.

End RAM_FRAME.

Definition SingleFrame' := RAM_FRAME.SingleFrame'.
Definition SingleFrame := RAM_FRAME.SingleFrame.

Arguments RAM_FRAME.Build_SingleFrame' {l} {g} {s} frame frame_sound frame_closed.

Section SEMAX.

Context {Espec: OracleKind}.
Context {cs: compspecs}.

Inductive add_stats (s0: statement) : list SingleFrame -> list SingleFrame -> Prop :=
  | add_stats_nil : add_stats s0 nil nil
  | add_stats_cons : forall l g s f fs fs' fc fc' F F', add_stats s0 F F' ->
      add_stats s0
       (RAM_FRAME.Build_SingleFrame l g s (RAM_FRAME.Build_SingleFrame' f fs fc) :: F)
       (RAM_FRAME.Build_SingleFrame l g (s0 :: s) (RAM_FRAME.Build_SingleFrame' f fs' fc') :: F')
  .

Definition SingleFrame'_inv {l g s0 s} (F: SingleFrame' l g (s0 :: s)) : SingleFrame' l g s :=
  match F with
  | RAM_FRAME.Build_SingleFrame' f fs fc =>
      RAM_FRAME.Build_SingleFrame' f fs (Forall_tl _ _ _ fc)
  end.

Lemma eexists_add_stats_cons: forall s0 l g s (F0: SingleFrame' _ _ _) F F',
  add_stats s0 F F' ->
  add_stats s0
   (RAM_FRAME.Build_SingleFrame l g s (SingleFrame'_inv F0) :: F)
   (RAM_FRAME.Build_SingleFrame l g (s0 :: s) F0 :: F').
Proof.
  intros.
  destruct F0; unfold SingleFrame'_inv.
  constructor.
  auto.
Qed.

Fixpoint semax_ram (Delta: tycontext) (F: list SingleFrame) (P: environ -> mpred) (c: statement) (Q: ret_assert): Prop :=
  match F with
  | nil => semax Delta P c Q
  | RAM_FRAME.Build_SingleFrame _ _ _ (RAM_FRAME.Build_SingleFrame' F0 _ _) :: F_tail =>
      semax_ram Delta F_tail (P * F0) c Q
  end.

Lemma semax_ram_pre: forall Delta F P P' c Q,
  P' |-- P ->
  semax_ram Delta F P c Q ->
  semax_ram Delta F P' c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  revert P P' H0 H; induction F; intros; simpl in H0 |- *.
Transparent LiftNatDed' LiftSepLog'.
  + eapply semax_pre0; eauto.
  + destruct a as [l g s [F0 ? ?]].
    eapply IHF; eauto.
    apply sepcon_derives; auto.
Qed.

Lemma semax_ram_localize: forall Delta F P c Q P',
  (exists F0: SingleFrame' P' P nil,
     semax_ram Delta (RAM_FRAME.Build_SingleFrame P' P nil F0 :: F) P' c Q) ->
  semax_ram Delta F P c Q.
Proof.
  intros.
  destruct H as [F0 ?].
  simpl in H.
  destruct F0 as [F0 ? ?].  
  eapply semax_ram_pre; eauto.
Qed.

Lemma semax_ram_unlocalize: forall Delta l g s F P c Q P'
  (frame_sound: g |-- l * (P -* P'))
  (frame_closed: Forall (fun s => closed_wrt_modvars s (P -* P')) s),
  semax_ram Delta F P' c Q ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame' (P -* P') frame_sound frame_closed) :: F) P c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto].
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma semax_ram_unlocalize': forall Delta l g s F P0 P1 P c Q P'
  (frame_sound: g |-- l * (P1 && (P -* P')))
  (frame_closed: Forall (fun s => closed_wrt_modvars s (P1 && (P -* P'))) s),
  corable P0 ->
  corable P1 ->
  semax_ram Delta F (P0 && P1 && P') c Q ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame' (P1 && (P -* P')) frame_sound frame_closed) :: F) (P0 && P) c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto].
  rewrite corable_andp_sepcon1 by auto.
  rewrite andp_assoc.
  apply andp_derives; [auto |].
  rewrite corable_sepcon_andp1 by auto. 
  apply andp_derives; [auto |].
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma SEPx_sepcon: forall P Q R, PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q TT) && SEPx R.
Proof.
  intros.
  unfold PROPx, LOCALx.
  rewrite andp_TT.
  rewrite andp_assoc.
  auto.
Qed.

Lemma corable_PROP_LOCAL: forall P Q R, corable R -> corable (PROPx P (LOCALx Q R)).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold PROPx, LOCALx.
  apply corable_andp; auto.
  unfold local, lift1.
  apply corable_andp; auto.
  unfold_lift.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl.
  intros.
  auto.
Qed.

Inductive split_by_closed:
 list statement -> list (environ -> Prop) -> list (environ -> Prop) -> list (environ -> Prop) -> Prop :=
 | split_by_closed_nil: forall s, split_by_closed s nil nil nil
 | split_by_closed_cons_closed: forall s q Q Q1 Q2,
     Forall (fun s => closed_wrt_modvars s (local q)) s ->
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) (q :: Q1) Q2
 | split_by_closed_cons_unclosed: forall s q Q Q1 Q2,
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) Q1 (q :: Q2).

Lemma insert_local': forall Q1 P Q R,
  local Q1 && (PROPx P (LOCALx Q R)) = (PROPx P (LOCALx (Q1 :: Q) R)).
Proof.
intros. extensionality rho.
unfold PROPx, LOCALx, local; super_unfold_lift. simpl.
apply pred_ext; autorewrite with gather_prop; normalize;
decompose [and] H; clear H.
Qed.

Lemma split_by_closed_spec: forall s P Q Q1 Q2,
  split_by_closed s Q Q1 Q2 ->
  Forall (fun s => closed_wrt_modvars s (PROPx P (LOCALx Q1 TT))) s /\
  PROPx P (LOCALx Q TT) = PROPx P (LOCALx Q1 TT) && PROPx nil (LOCALx Q2 TT).
Proof.
  intros.
  split.
  + rewrite Forall_forall; intros.
    induction H.
    - auto with closed.
    - spec IHsplit_by_closed; auto.
      rewrite Forall_forall in H; specialize (H x H0).
      rewrite <- insert_local'.
      auto with closed.
    - auto.
  + induction H.
    - apply add_andp.
      change (PROP  ()  LOCAL ()  TT) with (TT && (local (`True) && TT)).
      unfold local, lift1; unfold_lift; simpl; intros.
      repeat apply andp_right; apply prop_right; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite andp_assoc; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite <- !andp_assoc.
      rewrite (andp_comm (local q)); auto.
Qed.

Lemma frame_sound_aux: forall g l R P' Q1' R',
  g |-- PROPx P' (LOCALx Q1' TT) ->
  g |-- l * (SEPx R -* SEPx R') ->
  g |-- l * (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R')).
Proof.
  intros.
  rewrite corable_sepcon_andp1 by (apply corable_PROP_LOCAL; simpl; auto).
  apply andp_right; auto.
Qed.

Lemma frame_closed_aux: forall s R P' Q' Q1' Q2' R',
  split_by_closed s Q' Q1' Q2' ->
  Forall (fun s => closed_wrt_modvars s (SEPx R -* SEPx R')) s ->
  Forall (fun s => closed_wrt_modvars s (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R'))) s.
Proof.
  intros.
  apply split_by_closed_spec with (P := P') in H.
  destruct H as [? _].
  rewrite Forall_forall in *.
  intros x HH; specialize (H x HH); specialize (H0 x HH).
  auto with closed.
Qed.

Lemma semax_ram_unlocalize_PROP_LOCAL_SEP: forall Delta l g s F P Q R c Ret P' Q' Q1' Q2' R'
  (SPLIT: split_by_closed s Q' Q1' Q2')
  (SEP_frame_sound: g |-- l * (SEPx R -* SEPx R'))
  (SEP_frame_closed: Forall (fun s => closed_wrt_modvars s (SEPx R -* SEPx R')) s)
  (PURE_frame_sound: g |-- PROPx P' (LOCALx Q1' TT)),
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx nil (LOCALx Q2' TT) ->
  semax_ram Delta F (PROPx P' (LOCALx Q' (SEPx R'))) c Ret ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame'
       (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R'))
       (frame_sound_aux _ _ _ _ _ _ PURE_frame_sound SEP_frame_sound)
       (frame_closed_aux _ _ _ _ _ _ _ SPLIT SEP_frame_closed)) :: F)
   (PROPx P (LOCALx Q (SEPx R))) c Ret.
Proof.
  intros.
  eapply semax_ram_pre with (PROPx nil (LOCALx Q2' (SEPx R))).
  1: rewrite SEPx_sepcon with (Q := Q2'); apply andp_right;
       [eauto | rewrite SEPx_sepcon; apply andp_left2; auto].
  rewrite SEPx_sepcon in H |- *.
  apply semax_ram_unlocalize';
   [ apply corable_PROP_LOCAL; simpl; auto
   | apply corable_PROP_LOCAL; simpl; auto
   |].
  apply split_by_closed_spec with (P := P') in SPLIT.
  rewrite (andp_comm (PROP  ()  (LOCALx Q2' TT))), <- (proj2 SPLIT).
  rewrite SEPx_sepcon in H0; auto.
Qed.

Lemma semax_ram_abduction: forall Delta l g s F P c Q F0
  (frame_sound: g |-- l * F0)
  (frame_closed: Forall (fun s => closed_wrt_modvars s F0) s),
  semax_ram Delta F (P * F0) c Q ->
  semax_ram Delta
    (RAM_FRAME.Build_SingleFrame l g s
      (RAM_FRAME.Build_SingleFrame' F0 frame_sound frame_closed) :: F) P c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto]; auto.
Qed.

Lemma semax_ram_seq_skip:
  forall Delta F P c Q,
  semax_ram Delta F P c Q <-> semax_ram Delta F P (Ssequence c Sskip) Q.
Proof.
  intros.
  revert P Q; induction F; intros.
  + unfold semax_ram.
    apply semax_seq_skip.
  + destruct a; destruct real_frame; simpl.
    apply IHF.
Qed.
  
Lemma semax_ram_seq: forall Delta F F' P Q R c0 c1,
  add_stats c0 F F' ->
  semax Delta P c0 (normal_ret_assert Q) ->
  semax_ram (update_tycon Delta c0) F' Q c1 R ->
  semax_ram Delta F P (Ssequence c0 c1) R.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  revert P Q H0 H1; induction H; intros; simpl in H1 |- *.
Transparent LiftNatDed' LiftSepLog'.
  + eapply semax_seq'; eauto.
  + eapply IHadd_stats; [| eauto].
    rewrite <- frame_normal.
    apply semax_frame; auto.
    inversion fc'; subst; auto.
Qed.

Lemma semax_ram_seq': forall Delta F F' P Q R c,
  add_stats c F F' ->
  semax Delta P c (normal_ret_assert Q) ->
  semax_ram (update_tycon Delta c) F' Q Sskip R ->
  semax_ram Delta F P c R.
Proof.
  intros.
  rewrite semax_ram_seq_skip.
  eapply semax_ram_seq;
  eauto.
Qed.

Lemma ram_seq_assoc: forall Delta F P s1 s2 s3 R,
  semax_ram Delta F P (Ssequence s1 (Ssequence s2 s3)) R <->
  semax_ram Delta F P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
  induction F; intros.
  + apply seq_assoc.
  + simpl.
    destruct a as [l g s [F0 ? ?]].
    apply IHF; auto.
Qed.

Lemma ram_extract_exists_pre: forall A Delta F P c Q,
  (forall x : A, semax_ram Delta F (P x) c Q) ->
  semax_ram Delta F (EX  x : A, P x) c Q.
Proof.
Opaque LiftNatDed' LiftSepLog'.
  induction F; intros; simpl in H |- *.
Transparent LiftNatDed' LiftSepLog'.
  + apply extract_exists_pre; auto.
  + destruct a as [l g s [F0 ? ?]].
    rewrite exp_sepcon1.
    apply IHF; auto.
Qed.

Lemma revert_exists_left: forall {A} (x : A) P (Q: environ -> mpred),
  (EX  x : A, P x) |-- Q ->
  (P x) |-- Q.
Proof.
  intros.
  eapply derives_trans; [| eauto].
  apply (exp_right x); auto.
Qed.

Lemma revert_prop_left: forall {PureF: Prop},
  PureF -> 
  forall P Q R Post,
  PROPx (PureF :: P) (LOCALx Q (SEPx R)) |-- Post ->
  PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [| eauto].
  unfold PROPx; simpl; intros; normalize.
Qed.

Lemma ram_revert_exists_pre: forall {A} (x : A) Delta F P c Q,
  semax_ram Delta F (EX  x : A, P x) c Q ->
  semax_ram Delta F (P x) c Q.
Proof.
  intros.
  eapply semax_ram_pre; [| eauto].
  apply (exp_right x); auto.
Qed.

Lemma ram_revert_prop_pre: forall {PureF: Prop},
  PureF -> 
  forall Delta F P c Q,
  semax_ram Delta F (!! PureF && P) c Q ->
  semax_ram Delta F P c Q.
Proof.
  intros.
  eapply semax_ram_pre; [| eauto].
  normalize.
Qed.
  
End SEMAX.

Arguments SingleFrame' {l} {g} {s}.

