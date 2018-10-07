Require Import RamifyCoq.lib.Equivalence_ext.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import VST.floyd.base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.forward_lemmas.
Local Open Scope logic.

Section RAMIFICATION.

Context {CS: compspecs}.
Context (Espec: OracleKind).

Lemma semax_ramification: forall Delta G L s L' G',
  closed_wrt_modvars s (L' -* G') ->
  G |-- L * (L' -* G') ->
  semax Delta L s (normal_ret_assert L') ->
    semax Delta G s (normal_ret_assert G').
Proof.
  intros.
  apply semax_pre_post with (P' := L * (L' -* G')) (R' := normal_ret_assert (L' * (L' -* G'))). 
  + intros.
    apply andp_left2; auto.
  + intros.
    apply andp_left2.
    unfold normal_ret_assert.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite sepcon_comm, wand_sepcon_adjoint; auto.
  + apply semax_frame with (F := L' -* G') in H1; [| auto].
    rewrite frame_normal in H1.
    auto.
Qed.

Lemma corable_local: forall P, corable (local P).
Proof.
  intros.
  simpl; intros.
  unfold local, lift1.
  apply corable_prop.
Qed.

Definition vars_relation (S: ident -> Prop) (rho rho': environ) : Prop :=
  (forall i : ident, S i \/ Map.get (te_of rho) i = Map.get (te_of rho') i) /\
  (exists te', rho' = mkEnviron (ge_of rho) (ve_of rho) te').

Instance vars_relation_Reflexive (S: ident -> Prop): Reflexive (vars_relation S).
Proof.
  hnf; intros.
  split.
  + auto.
  + exists (te_of x).
    destruct x; reflexivity.
Defined.

Instance vars_relation_Symmetric (S: ident -> Prop): Symmetric (vars_relation S).
Proof.
  hnf; intros.
  destruct H.
  split.
  + intro i; specialize (H i).
    destruct H; [left; auto | right; congruence].
  + exists (te_of x).
    destruct H0, x, y.
    inversion H0; subst.
    reflexivity.
Defined.

Instance vars_relation_Transitive (S: ident -> Prop): Transitive (vars_relation S).
Proof.
  hnf; intros.
  destruct H, H0.
  split.
  + intro i; specialize (H i); specialize (H0 i).
    destruct H, H0; try solve [left; auto].
    right.
    congruence.
  + exists (te_of z).
    destruct H1, H2, x, y, z.
    inversion H1; inversion H2; subst.
    reflexivity.
Defined.

Instance vars_relation_Equivalence (S: ident -> Prop): Equivalence (vars_relation S).
Proof.
  split.
  apply vars_relation_Reflexive.
  apply vars_relation_Symmetric.
  apply vars_relation_Transitive.
Defined.
  
Lemma EnvironStable_var_relation_closed: forall S (P: environ -> mpred),
  EnvironStable (vars_relation S) P <-> closed_wrt_vars S P.
Proof.
  intros.
  unfold EnvironStable, vars_relation, closed_wrt_vars.
  split.
  + intros.
    specialize (H rho (mkEnviron (ge_of rho) (ve_of rho) te')).
    apply H.
    split; eauto.
  + intros.
    destruct H0 as [? [? ?]].
    subst rho'.
    apply H; auto.
Qed.

Definition ModBox (c: statement) := EnvironBox (vars_relation (modifiedvars c)).

Lemma go_lower_ModBox: forall c P rho, ModBox c P rho = ALL  rho' : environ , !!vars_relation (modifiedvars c) rho rho' --> P rho'.
Proof. intros. reflexivity. Qed.

Lemma semax_ramification_P: forall Delta c (G L L' G': environ -> mpred),
  G |-- L * ModBox c (L' -* G') ->
  semax Delta L c (normal_ret_assert L') ->
  semax Delta G c (normal_ret_assert G').
Proof.
  intros.
  apply semax_pre_post with
    (P' := L * ModBox c (L' -* G'))
    (R' := normal_ret_assert (L' * ModBox c (L' -* G'))). 
  + intros.
    apply andp_left2.
    auto.
  + intros.
    apply andp_left2.
    apply normal_ret_assert_derives'.
    rewrite sepcon_comm, wand_sepcon_adjoint; auto.
    apply EnvironBox_T.
    apply vars_relation_Equivalence.
  + apply semax_frame with (F := ModBox c (L' -* G')) in H0.
    -
    rewrite frame_normal in H0.
    auto.
    - apply EnvironStable_var_relation_closed.
      apply EnvironBox_EnvironStable.
      apply vars_relation_Equivalence.
Qed.

Lemma semax_ramification_Q: forall A Delta G L s (L' G': A -> _),
  (forall x, closed_wrt_modvars s (L' x -* G' x)) ->
  G |-- L * allp (L' -* G') ->
  semax Delta L s (normal_ret_assert (exp L')) ->
    semax Delta G s (normal_ret_assert (exp G')).
Proof.
  intros.
  apply semax_pre_post with
   (P' := L * allp (L' -* G'))
   (R' := normal_ret_assert (exp L' * allp (L' -* G'))). 
  + intros.
    apply andp_left2; auto.
  + intros.
    apply andp_left2.
    apply normal_ret_assert_derives'.
    rewrite exp_sepcon1.
    apply exp_left; intro x; apply (exp_right x).
    rewrite sepcon_comm, wand_sepcon_adjoint.
    apply (allp_left _ x); auto.
  + apply semax_frame with (F := allp (L' -* G')) in H1; [| auto with closed].
    rewrite frame_normal in H1.
    auto.
Qed.

Lemma semax_ramification_PQ: forall A Delta c G L (L' G': A -> _),
  G |-- L * ModBox c (allp (L' -* G')) ->
  semax Delta L c (normal_ret_assert (exp L')) ->
  semax Delta G c (normal_ret_assert (exp G')).
Proof.
  intros.
  apply ramify_PQ_reduce0 in H.
  eapply semax_ramification_P; eauto.
Qed.

End RAMIFICATION.

