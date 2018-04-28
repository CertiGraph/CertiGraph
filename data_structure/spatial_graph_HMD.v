Require Import RamifyCoq.msl_application.Graph.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.precise_direct.
Require Import RamifyCoq.msl_ext.overlapping_direct.
Require Import RamifyCoq.msl_ext.alg_seplog_direct.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.
Require Import RamifyCoq.heap_model_direct.mapsto.
Require Import RamifyCoq.heap_model_direct.SeparationLogic.
Require Import VST.msl.msl_direct.
Require Import VST.msl.predicates_sa.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.Znumtheory.

Local Open Scope nat.
Local Open Scope pred.

Instance SGS_HMD: PointwiseGraphSetting.
  apply (Build_PointwiseGraphSetting adr 0 eq_nat_dec).
Defined.

Definition trinode x (dlr: bool * nat * nat) :=
  match dlr with
  | (d, l, r) => !! Z.divide 3 (Z.of_nat x) && ((mapsto x (if d then 1 else 0)) * (mapsto (x+1) l) * (mapsto (x+2) r))
  end.

Lemma trinode_unfold: forall x, exp (trinode x) = !! Z.divide 3 (Z.of_nat x) && ((EX d: bool, (mapsto x (if d then 1 else 0))) * (exp (mapsto (x + 1))) * (exp (mapsto (x + 2)))).
Proof.
  intros.
  replace (exp (trinode x) =
   !! Z.divide 3 (Z.of_nat x) && ((EX d: bool, (mapsto x (if d then 1 else 0))) * exp (mapsto (x + 1)) * exp (mapsto (x + 2)))) with
    ((EX dlr : bool * adr * adr,
      !! Z.divide 3 (Z.of_nat x) &&
      (mapsto x (if (fst (fst dlr)) then 1 else 0) * mapsto (x + 1) (snd (fst dlr)) *
       mapsto (x + 2) (snd dlr))) =
   !! Z.divide 3 (Z.of_nat x) && ((EX d: bool, (mapsto x (if d then 1 else 0))) * seplog.exp (mapsto (x + 1)) * seplog.exp (mapsto (x + 2))))%logic.
  2: {
    f_equal.
    simpl.
    f_equal.
    extensionality dlr; destruct dlr as [[? ?] ?]. reflexivity.
  }
  rewrite <- log_normalize.exp_andp2.
  f_equal.
  repeat rewrite exp_curry; simpl fst; simpl snd.
  rewrite seplog.sepcon_assoc.
  rewrite log_normalize.exp_sepcon1.
  f_equal. extensionality s.
  rewrite log_normalize.exp_sepcon1.
  rewrite log_normalize.exp_sepcon2.
  f_equal; extensionality l.
  rewrite !log_normalize.exp_sepcon2.
  f_equal; extensionality r.
  rewrite seplog.sepcon_assoc.
  reflexivity.
Qed.

Lemma mapsto_derives_aux: forall x, EX  d : bool, mapsto x (if d then 1 else 0) |-- exp (mapsto x).
Proof.
  intros.
  apply exp_left; intro d.
  apply (exp_right (if d then 1 else 0)); auto.
Qed.

Lemma trinode__precise: forall x, precise (exp (trinode x)).
Proof.
  intros.
  rewrite trinode_unfold.
  pose proof (@precise_andp_right _ _ _ PSLdirect).
  simpl in H.
  apply H.
  repeat apply precise_sepcon; try apply mapsto__precise.
  apply derives_precise with (exp (mapsto x)); [| apply mapsto__precise].
  apply mapsto_derives_aux.
Qed.

Lemma trinode_conflict: forall p1 p2 v1 v2, p1 = p2 -> trinode p1 v1 * trinode p2 v2 |-- FF.
Proof.
  intros.
  destruct v1 as [[d1 l1] r1].
  destruct v2 as [[d2 l2] r2].
  change (trinode p1 (d1, l1, r1) * trinode p2 (d2, l2, r2) |-- FF) with
   (seplog.derives (!! Z.divide 3 (Z.of_nat p1) && (mapsto p1 (if d1 then 1 else 0) * mapsto (p1 + 1) l1 * mapsto (p1 + 2) r1) *
   (!! Z.divide 3 (Z.of_nat p2) && (mapsto p2 (if d2 then 1 else 0) * mapsto (p2 + 1) l2 * mapsto (p2 + 2) r2)))
    FF)%logic.
  eapply seplog.derives_trans.
  + apply seplog.sepcon_derives;
    (apply log_normalize.andp_derives;
    [| apply seplog.sepcon_derives; [apply seplog.sepcon_derives | apply seplog.derives_refl ]]);
    apply TT_right.
  + rewrite !TT_andp.
    simpl.
    rewrite !sepcon_assoc.
    rewrite (sepcon_comm (mapsto (p1 + 2) r1)).
    rewrite !sepcon_assoc.
    pose proof sepcon_left2_corable_right as HH; simpl in HH.
    do 4 (try apply HH); try apply corable_prop.
    apply mapsto_conflict.
    congruence.
Qed.

Lemma align_3_aux: forall x, Z.divide 3 (Z.of_nat x) <-> exists k, x = (k * 3) % nat.
Proof.
  intros.
  unfold Z.divide.
  split; intros [?k ?].
  + exists (Z.to_nat k).
    rewrite <- (Nat2Z.id x).
    rewrite H.
    assert (0 <= k)%Z.
    1: {
      destruct (Z_lt_le_dec k 0%Z); auto.
      assert (k * 3 < 0 * 3)%Z by (apply Z.mul_lt_mono_pos_r; omega).
      simpl in H0.
      omega.
    }
    apply Z2Nat.inj_mul; omega.
  + exists (Z.of_nat k).
    rewrite H.
    apply Nat2Z.inj_mul.
Qed.

Lemma align_3_aux1: forall p1 p2 k1 k2, (p1 = k1 * 3 -> p2 = k2 * 3 -> p1 = p2 + 1 -> False)%nat.
Proof.
  intros.
  subst.
  destruct (le_dec k1 k2).
  + pose proof mult_le_compat_r _ _ 3 l.
    omega.
  + assert (k2 * 3 < k1 * 3) by (apply Nat.mul_lt_mono_pos_r; omega).
    omega.
Qed.

Lemma align_3_aux2: forall p1 p2 k1 k2, (p1 = k1 * 3 -> p2 = k2 * 3 -> p1 = p2 + 2 -> False)%nat.
Proof.
  intros.
  subst.
  destruct (le_dec k1 k2).
  + pose proof mult_le_compat_r _ _ 3 l.
    omega.
  + assert (k2 * 3 < k1 * 3) by (apply Nat.mul_lt_mono_pos_r; omega).
    omega.
Qed.

Lemma disj_trinode_: forall p1 p2, p1 <> p2 -> disjointed (EX  v : bool * adr * adr, trinode p1 v)
  (EX  v : bool * adr * adr, trinode p2 v).
Proof.
  intros.
  change (EX  v : bool * adr * adr, trinode p1 v) with (exp (trinode p1)).
  change (EX  v : bool * adr * adr, trinode p2 v) with (exp (trinode p2)).
  rewrite !trinode_unfold.
  pose proof disj_prop_andp_left as HH; simpl in HH; apply HH; clear HH; [apply Zdivide_dec |].
  intros.
  apply align_3_aux in H0; destruct H0 as [k1 ?].
  pose proof disj_prop_andp_right as HH; simpl in HH; apply HH; clear HH; [apply Zdivide_dec |].
  intros.
  apply align_3_aux in H1; destruct H1 as [k2 ?].
  pose proof disj_sepcon_right as HH; simpl in HH.
  repeat apply HH; apply disj_comm; repeat apply HH;
  try (eapply disj_derives;
         [ first [apply mapsto_derives_aux | apply derives_refl]
         | first [apply mapsto_derives_aux | apply derives_refl]
         | apply disj_mapsto_]; omega).
Qed.

Lemma trinode_inj: forall p v1 v2, trinode p v1 && trinode p v2 |-- !! (v1 = v2).
Proof.
  intros.
  unfold trinode.
  destruct v1 as [[d1 l1] r1].
  destruct v2 as [[d2 l2] r2].
  eapply derives_trans.
  + apply andp_derives;
    (apply andp_derives;
    [apply (@TT_right _ Ndirect) | apply derives_refl]).
  + pose proof TT_andp.
    simpl in H; rewrite !H; clear H.
    rewrite !sepcon_assoc.
    eapply derives_trans.
    apply precise_left_sepcon_andp_distr with (exp (mapsto p)).
    1: apply mapsto__precise.
    1: apply (exp_right (if d1 then 1 else 0)); auto.
    1: apply (exp_right (if d2 then 1 else 0)); auto.
    
    eapply derives_trans; [apply sepcon_derives |].
    1: apply mapsto_inj.

    eapply derives_trans.
    apply precise_left_sepcon_andp_distr with (exp (mapsto (p + 1))).
    1: apply mapsto__precise.
    1: apply (exp_right l1); auto.
    1: apply (exp_right l2); auto.
        
    eapply derives_trans; [apply sepcon_derives |].
    1: apply mapsto_inj.
    1: apply mapsto_inj.
    1: apply derives_refl.
    
    pose proof sepcon_prop_prop.
    simpl in H; rewrite !H; clear H.

    intro; simpl in *; intros.
    unfold prop in *.
    
    destruct d1, d2; destruct H as [? [? ?]]; congruence.
Qed.

Instance MSLdirect : MapstoSepLog AV_SGraph trinode.
Proof.
  apply mkMapstoSepLog.
  apply trinode__precise.
Defined.

Instance sMSLdirect : StaticMapstoSepLog AV_SGraph trinode.
Proof.
  apply mkStaticMapstoSepLog; simpl; intros.
  + hnf in H. simpl in H. unfold addr_eqb in H. simpl in H.
    destruct eq_nat_dec.
    - inversion H.
    - exfalso; tauto.
  + apply trinode_conflict.
    unfold addr_eqb in H; simpl in H.
    destruct (eq_nat_dec p1 p2); congruence.
  + apply disj_trinode_.
    unfold addr_eqb in H; simpl in H.
    destruct (eq_nat_dec p1 p2); congruence.
Defined.

Instance nMSLdirect : NormalMapstoSepLog AV_SGraph trinode.
Proof.
  apply mkNormalMapstoSepLog.
  apply trinode_inj.
Defined.

Instance SGA_HMD: PointwiseGraphAssum.
  apply (Build_PointwiseGraphAssum (pred world) _ _ _ _ _ _ _ _ SGS_HMD trinode _ _ (* nMSLdirect *)).
Defined.