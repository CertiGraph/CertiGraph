Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.psepalg.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.
Require Import RamifyCoq.heap_model_direct.mapsto.
Require Import VST.msl.msl_direct.
Require Import VST.msl.predicates_sa.

Instance Ndirect : NatDed (pred world) := algNatDed world.
Instance Sdirect : SepLog (pred world) := algSepLog world.
Instance Cldirect : ClassicalSep (pred world) := algClassicalSep world.
Instance CSLdirect : CorableSepLog (pred world) := algCorableSepLog world.
Instance PSLdirect : PreciseSepLog (pred world) := algPreciseSepLog world.
Instance OSLdirect : OverlapSepLog (pred world) := algOverlapSepLog world.
Instance DSLdirect : DisjointedSepLog (pred world) := algDisjointedSepLog world.
Instance MSLdirect : MapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkMapstoSepLog. repeat intro.
  destruct H1 as [w3 ?], H2 as [w4 ?]; destruct H as [? [? [? ?]]], H0 as [? [? [? ?]]].
  destruct w1 as [v1 f1]; destruct w2 as [v2 f2]; destruct w3 as [v3 f3]; destruct w4 as [v4 f4]; destruct w as [v f].
  hnf in H1, H2; simpl in *. apply exist_ext. extensionality mm. destruct (eq_dec mm p).
  + subst. specialize (H1 p). specialize (H2 p). rewrite H4 in *. rewrite H6 in *. inversion H1.
    - subst. inversion H2.
      * rewrite H10, H12. auto.
      * subst. rewrite <- H8 in H2. rewrite <- H11 in H2. hnf in H2. inversion H2. subst. inversion H15.
    - subst. rewrite <- H8 in H1. rewrite <- H9 in H1. hnf in H1. inversion H1. subst. inversion H13.
  + specialize (H3 mm n). specialize (H5 mm n). rewrite H3, H5. auto.
Defined.

Instance sMSLdirect : StaticMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H. unfold adr_conflict in H. destruct (eq_nat_dec p p).
    - inversion H.
    - exfalso; tauto.
  + unfold adr_conflict in H. destruct (eq_nat_dec p1 p2).
    - subst. intro w. apply mapsto_unique.
    - inversion H.
  + unfold adr_conflict in H. destruct (eq_nat_dec p1 p2).
    - inversion H.
    - hnf. intros. destruct H2 as [v1 ?]. destruct H3 as [v2 ?].
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
        + rewrite e in *. rewrite H5. generalize (H6 p1 n); intro HS. rewrite HS. constructor.
        + destruct (eq_nat_dec z p2).
          - rewrite e in *. rewrite H7. generalize (H4 p2 n0); intro HS. rewrite HS. constructor.
          - specialize (H4 z n0). specialize (H6 z n1). rewrite H4, H6. constructor.
      } rewrite <- Heqw0 in *. rewrite <- Heqw in *.
      assert (emp h2). {
        apply join_sub_joins_identity with h23.
        + exists h3; auto.
        + try_join h2 h23 t. exists t; auto.
      } elim_emp_direct.
      split; auto. exists ff; auto.
Defined.

Instance nMSLdirect : NormalMapstoSepLog AbsAddr_world mapsto.
Proof.
  apply mkNormalMapstoSepLog. intros; simpl; intro w; intros. destruct H.
  destruct H as [? [? ?]]. destruct H0 as [? [? ?]]. rewrite H2 in H4.
  inversion H4. subst; auto.
Defined.
