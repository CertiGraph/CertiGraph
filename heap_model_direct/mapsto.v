Require Import VST.msl.msl_direct.
Require Import FunctionalExtensionality.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.msl_ext.overlapping_direct.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.

Definition mapsto (x y: adr) : pred world :=
  fun w => x <> 0 /\
    (forall a, a <> x -> lookup_fpm w a = None) /\
    lookup_fpm w x = Some y.

Lemma join_sub_mapsto: forall w1 w2 x y, join_sub w1 w2 -> (mapsto x y * TT)%pred w1 -> (mapsto x y * TT)%pred w2.
Proof.
  intros. destruct_sepcon H0 h. destruct H as [w3 ?]. try_join h2 w3 m. exists h1, m. split; auto.
Qed.

Lemma mapsto_unique: forall x a b w, ~ (mapsto x a * mapsto x b)%pred w.
Proof.
  repeat intro. destruct_sepcon H h. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]]. destruct h1 as [f1 m1].
  destruct h2 as [f2 m2]. destruct w as [fw mw]. hnf in *. simpl in *. specialize (H x). rewrite H3 in *. rewrite H5 in *.
  inversion H. inversion H9.
Qed.

Lemma mapsto__precise: forall p, precise (EX  v : adr, mapsto p v).
Proof.
  intros.
  repeat intro.
  destruct H1 as [w3 ?], H2 as [w4 ?]; destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  destruct w1 as [v1 f1]; destruct w2 as [v2 f2]; destruct w3 as [v3 f3]; destruct w4 as [v4 f4]; destruct w as [v f].
  hnf in H1, H2; simpl in *. apply exist_ext. extensionality mm. destruct (eq_dec mm p).
  + subst. specialize (H1 p). specialize (H2 p). rewrite H4 in *. rewrite H6 in *. inversion H1.
    - subst. inversion H2.
      * rewrite H10, H12. auto.
      * subst. rewrite <- H8 in H2. rewrite <- H11 in H2. hnf in H2. inversion H2. subst. inversion H15.
    - subst. rewrite <- H8 in H1. rewrite <- H9 in H1. hnf in H1. inversion H1. subst. inversion H13.
  + specialize (H3 mm n). specialize (H5 mm n). rewrite H3, H5. auto.
Qed.

Lemma mapsto_conflict: forall p1 p2 v1 v2, p1 = p2 -> mapsto p1 v1 * mapsto p2 v2 |-- FF.
Proof.
  intros.
  subst.
  intro w. apply mapsto_unique.
Qed.

Lemma disj_mapsto_: forall p1 p2, p1 <> p2 -> disjointed (EX v1: adr, mapsto p1 v1) (EX v2: adr, mapsto p2 v2).
Proof.
  intros.
  hnf. intros. destruct H2 as [v1 ?]. destruct H3 as [v2 ?].
  generalize H2; intro Hx. generalize H3; intro Hy.
  destruct h12 as [f12 x12] eqn:? . hnf in H2. simpl in H2. destruct H2 as [? [? ?]].
  destruct h23 as [f23 x23] eqn:? . hnf in H3. simpl in H3. destruct H3 as [? [? ?]].
  remember (fun xx : adr => if eq_nat_dec xx p1 then Some v1 else (if eq_nat_dec xx p2 then Some v2 else None)) as f.
  assert (finMap f). {
    exists (p1 :: p2 :: nil). intro z. intros. rewrite Heqf. destruct (eq_nat_dec z p1).
    + subst. exfalso. apply H8. apply in_eq.
    + destruct (eq_nat_dec z p2).
      - subst. exfalso. apply H8. apply in_cons, in_eq.
      - trivial.
  } remember (exist (finMap (B:=adr)) f H8) as ff.
  assert (join h12 h23 ff). {
    rewrite Heqw, Heqw0, Heqff. hnf; simpl. rewrite Heqf. intro z. destruct (eq_nat_dec z p1).
    + rewrite e in *. rewrite H5. generalize (H6 p1 H); intro HS. rewrite HS. constructor.
    + destruct (eq_nat_dec z p2).
      - rewrite e in *. rewrite H7. generalize (H4 p2 n); intro HS. rewrite HS. constructor.
      - specialize (H4 z n). specialize (H6 z n0). rewrite H4, H6. constructor.
  } rewrite <- Heqw0 in *. rewrite <- Heqw in *.
  assert (emp h2). {
    apply join_sub_joins_identity with h23.
    + exists h3; auto.
    + try_join h2 h23 t. exists t; auto.
  } elim_emp_direct.
  split; auto. exists ff; auto.
Qed.

Lemma mapsto_inj: forall p v1 v2, mapsto p v1 && mapsto p v2 |-- !! (v1 = v2).
Proof.
  intros; simpl; intro w; intros. destruct H.
  destruct H as [? [? ?]]. destruct H0 as [? [? ?]]. rewrite H2 in H4.
  inversion H4. subst; auto.
Qed.
