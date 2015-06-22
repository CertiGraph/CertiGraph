Require Import VST.floyd.base.
Require Import VST.floyd.canon.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import RamifyCoq.veric_ext.seplog.
Require Import RamifyCoq.veric_ext.SeparationLogic.

Local Open Scope logic.

Section SEMAX.

Context {Espec: OracleKind}.

Record SingleFrame: Type := {
  local_assert: environ -> mpred;
  global_assert: environ -> mpred;
  stats: list statement
}.

Definition add_stat s0 (f: SingleFrame) :=
  Build_SingleFrame (local_assert f) (global_assert f) (s0 :: (stats f)).

Definition add_stats s0 fs := map (add_stat s0) fs.

Fixpoint semax_ram (Delta: tycontext) (F: list SingleFrame) (P: environ -> mpred) (c: statement) (Q: ret_assert): Prop :=
  match F with
  | nil => semax Delta P c Q
  | Build_SingleFrame l g s :: F_tail =>
      exists F0,
        g |-- l * F0 /\
        Forall (fun s => closed_wrt_modvars s F0) s /\
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
  + destruct a as [l g s].
    destruct H0 as [F0 [? [? ?]]].
    exists F0.
    split; [| split]; auto. 
    eapply IHF; eauto.
    apply sepcon_derives; auto.
Qed.

Lemma semax_ram_localize: forall Delta F P c Q P',
  semax_ram Delta (Build_SingleFrame P' P nil :: F) P' c Q ->
  semax_ram Delta F P c Q.
Proof.
  intros.
  destruct H as [F0 [? [_ ?]]].
  eapply semax_ram_pre; eauto.
Qed.

Lemma semax_ram_unlocalize: forall Delta l g s F P c Q P',
  semax_ram Delta F P' c Q ->
  g |-- l * (P -* P') ->
  Forall (fun s => closed_wrt_modvars s (P -* P')) s ->
  semax_ram Delta (Build_SingleFrame l g s :: F) P c Q.
Proof.
  intros.
  exists (P -* P').
  split; [| split]; auto.
  eapply semax_ram_pre; [| eauto].
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma semax_ram_abduction: forall Delta l g s F P c Q
  (abd: sigT (fun F0 => g = l * F0)),
  semax_ram Delta F (P * (projT1 abd)) c Q ->
  Forall (fun s => closed_wrt_modvars s (projT1 abd)) s ->
  semax_ram Delta (Build_SingleFrame l g s :: F) P c Q.
Proof.
  intros.
  destruct abd as [F0 ?].
  exists F0.
  split; [| split]; auto.
  subst; auto.
Qed.

Lemma semax_ram_seq: forall Delta F P Q R c0 c1,
  semax Delta P c0 (normal_ret_assert Q) ->
  semax_ram (update_tycon Delta c0) (add_stats c0 F) Q c1 R ->
  semax_ram Delta F P (Ssequence c0 c1) R.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  revert P Q H0 H; induction F; intros; simpl in H0 |- *.
Transparent LiftNatDed' LiftSepLog'.
  + eapply semax_seq'; eauto.
  + destruct a as [l g s].
    destruct H0 as [F0 [? [? ?]]].
    exists F0; split; [| split; [inversion H1 |]]; auto.
    eapply IHF; [eauto |].
    rewrite <- frame_normal.
    apply semax_frame; auto.
    inversion H1; subst; auto.
Qed.

End SEMAX.
