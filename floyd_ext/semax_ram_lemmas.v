Require Import RamifyCoq.Coqlib.
Require Import VST.floyd.base.
Require Import VST.floyd.canon.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.

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
      RAM_FRAME.Build_SingleFrame' f fs (Coqlib.Forall_tl _ _ _ fc)
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

Lemma semax_ram_unlocalize': forall Delta l g s F P0 P c Q P'
  (frame_sound: g |-- l * (P -* P'))
  (frame_closed: Forall (fun s => closed_wrt_modvars s (P -* P')) s),
  corable P0 ->
  semax_ram Delta F (P0 && P') c Q ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame' (P -* P') frame_sound frame_closed) :: F) (P0 && P) c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto].
  rewrite corable_andp_sepcon1 by auto.
  apply andp_derives; [auto |].
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma semax_ram_unlocalize'_PROP_LOCAL_SEP: forall Delta l g s F P Q R c Ret P' Q' R'
  (frame_sound: g |-- l * (SEPx R -* SEPx R'))
  (frame_closed: Forall (fun s => closed_wrt_modvars s (SEPx R -* SEPx R')) s)
  (pure_sound: PROPx P (LOCALx Q (SEPx R)) |-- PROPx P' (LOCALx Q' TT)),
  semax_ram Delta F (PROPx P' (LOCALx Q' (SEPx R'))) c Ret ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame' (SEPx R -* SEPx R') frame_sound frame_closed) :: F)
   (PROPx P (LOCALx Q (SEPx R))) c Ret.
Proof.
  intros.
Abort.

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
  
End SEMAX.
