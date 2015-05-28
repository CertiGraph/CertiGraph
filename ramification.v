Require Import msl.msl_direct.
Require Import overlapping.
Require Import ramify_tactics.
Require Import msl.sepalg_list.
Require Import msl_ext.
Require Import Classical.
Require Import Permutation.

Tactic Notation "LEM" constr(v) := (destruct (classic v); auto).

Definition ramify {A: Type}{JA: Join A}{PA: Perm_alg A}
           (R P Q R' : pred A) := R |-- P * (Q -* R').

Lemma ocon_ramification {A: Type}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}:
  forall P Q R R' F, precise P -> precise Q -> ramify (P ⊗ R) P Q (Q ⊗ R') ->
                     ramify ((P * F) ⊗ R) P Q ((Q * F) ⊗ R').
Proof.
  repeat intro; destruct_ocon H2 h; destruct_sepcon H5 x; destruct_cross h12.
  try_join h1x1 h2 h1x1h2; try_join h1x1h2 h3 h1x1h2h3; try_join h1x1 h2x1 x1'; equate_join x1 x1'.
  try_join h2x2 h3 h2x2h3; try_join_through h1x1h2 h2x2 h3 h2x2h3'; equate_join h2x2h3 h2x2h3'.
  assert (HPR: (P ⊗ R)%pred h1x1h2h3) by (simpl; exists h1x1, h2x1, h2x2h3, x1, h23; split; auto).
  specialize (H1 h1x1h2h3 HPR). destruct H1 as [x1' [h2x2h3' [? [? ?]]]]. equate_precise x1 x1'. equate_canc h2x2h3 h2x2h3'.
  try_join x2 h3 x2h3; exists x1, x2h3; repeat split; auto.
  intros m x2h3m; intros. try_join h2x2 h3 h2x2h3'; equate_join h2x2h3 h2x2h3'.
  try_join h2x2h3 m h2x2h3m; assert (HQR': (Q ⊗ R')%pred h2x2h3m) by (apply (H22 m); auto).
  destruct_ocon HQR' m. equate_precise m m12; equate_canc h2x2h3 m3.
  try_join h2x2 m2 h2x2m2. try_join h1x2 h2x2 x2'; equate_join x2 x2'. try_join x2 m x2m. try_join m1 x2 m1x2.
  try_join h1x2 m1 h1x2m1. exists h1x2m1, h2x2m2, h3, x2m, m23; repeat split; auto.
  try_join h2x2 m2 h2x2m2'; equate_join h2x2m2 h2x2m2'; auto.
  exists m, x2; split; auto.
Qed.

Lemma andp_ramification1 {A: Type}{JA: Join A}{PA: Perm_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}:
  forall P Q R R' F, precise P -> ramify R P Q R' -> ramify ((P * F) && R) P Q ((Q * F) && R').
Proof.
  intros; hnf; intros; destruct H1 as [[y [z [? [? ?]]]] ?].
  specialize (H0 a H4); destruct H0 as [y' [z' [? [? ?]]]]; equate_precise y y'; equate_canc z z'.
  exists y, z; do 2 (split; auto); intros z' m z'm; intros. specialize (H6 z' m z'm H0).
  split; auto. exists z', z; repeat split; auto.
Qed.

Notation "P '-⊛' Q" := (ewand P Q) (at level 60, right associativity) : pred.

Lemma andp_ramification2 {A: Type}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall P Q R R' F, (P -⊛ R |-- Q -* R') -> ramify ((P * F) && R) P Q ((Q * F) && R').
Proof.
  intros; hnf; intros; destruct H0 as [[y [z [? [? ?]]]] ?].
  assert ((P -⊛ R)%pred z) by (exists y, a; repeat split; auto).
  specialize (H z H4); exists y, z; do 2 (split; auto).
  intros m zm; intros; specialize (H m zm H5 H6).
  split; auto; exists m, z; repeat split; auto.
Qed.

Lemma disjoint_ramificatin {A: Type}{JA: Join A}{PA: Perm_alg A}:
  forall R P P' R' S Q Q' S', ramify R P P' R' -> ramify S Q Q' S' -> ramify (R * S) (P * Q) (P' * Q') (R' * S').
Proof.
  intros; hnf; intro ab; intros; destruct H1 as [a [b [? [? ?]]]].
  specialize (H a H2); specialize (H0 b H3).
  destruct H as [a1 [a2 [? [? ?]]]]; destruct H0 as [b1 [b2 [? [? ?]]]].
  try_join a1 b a1b; try_join a1 b1 a1b1; try_join a2 b2 a2b2.
  exists a1b1, a2b2; repeat split; auto. exists a1, b1; repeat split; auto. hnf.
  intros s1s2 w1w2; intros; destruct_sepcon H15 s.
  try_join a2 s1s2 a2s1s2; try_join a2 s1 a2s1; try_join b2 s2 b2s2.
  assert (R' a2s1) by (apply (H5 s1); auto); assert (S' b2s2) by (apply (H7 s2); auto).
  exists a2s1, b2s2; repeat split; auto.
Qed.

Lemma ocon_piecewise_ramification {A: Type}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}:
  forall P P' Q1 Q2 Q1' Q2', precise P -> precise P' -> ramify (P ⊗ Q1) P P' (P' ⊗ Q1') -> ramify (P ⊗ Q2) P P' (P' ⊗ Q2')
                             -> ramify (P ⊗ Q1 ⊗ Q2) P P' (P' ⊗ Q1' ⊗ Q2').
Proof.
  intros; hnf; intros.
  destruct H3 as [h124 [h567 [h3 [h124567 [h3567 [? [? [? [[h15 [h47 [h26 [h1457 [h2467 [? [? [? [? ?]]]]]]]]] ?]]]]]]]]].
  destruct (cross_split _ _ _ _ _ H3 H8) as [[[[h14 h2] h57] h6] [? [? [? ?]]]].
  destruct (cross_split _ _ _ _ _ H6 H14) as [[[[h1 h5] h4] h7] [? [? [? ?]]]].
  try_join h26 h3 h236; exists h1457, h236; repeat split; auto.
  assert (HPQ1: (P ⊗ Q1)%pred h124567) by (exists h15, h47, h26, h1457, h2467; repeat split; auto).
  specialize (H1 h124567 HPQ1); destruct H1 as [h1457' [h26' [? [? ?]]]]; equate_precise h1457 h1457'; equate_canc h26 h26'.
  assert (join h14 h57 h1457) by (apply (cross_rev h1 h5 h4 h7 h15 h47); auto).
  try_join h3 h6 h36; try_join h36 h1457 h134567; try_join h14 h36 h1346.
  try_join_through h1346 h14 h57 h1457'; equate_join h1457 h1457'.
  try_join h3 h57 h357; try_join_through h357 h3 h6 h36'; equate_join h36 h36'.
  assert (HPQ2: (P ⊗ Q2)%pred h134567) by (exists h14, h57, h36, h1457, h3567; repeat split; auto).
  specialize (H2 h134567 HPQ2); destruct H2 as [h1457' [h36' [? [? ?]]]]; equate_precise h1457 h1457'; equate_canc h36 h36'.
  intros h1457' a'; intros.
  (* destruct (nec_join2 H20 H2) as [h26' [h3' [? [? ?]]]]; destruct (nec_join2 H15 H37) as [h2' [h6' [? [? ?]]]]. *)
  (* try_join h3' h6' h36'; assert (necR h36 h36') by (apply (join_necR h3 h6 _ h3' h6' _); auto). *)
  try_join h26 h1457' h124567'; try_join h36 h1457' h134567'.
  assert (HPQ1': (P' ⊗ Q1')%pred h124567') by (apply (H23 h1457'); auto).
  assert (HPQ2': (P' ⊗ Q2')%pred h134567') by (apply (H34 h1457'); auto).
  destruct HPQ1' as [h15' [h47' [h26'' [h1457'' [h2467' [? [? [? [? ?]]]]]]]]].
  equate_precise h1457' h1457''; equate_canc h26 h26''.
  destruct HPQ2' as [h14' [h57' [h36'' [h1457'' [h3567' [? [? [? [? ?]]]]]]]]].
  equate_precise h1457' h1457''; equate_canc h36 h36''.
  destruct (cross_split _ _ _ _ _ H39 H41) as [[[[h1' h5'] h4'] h7'] [? [? [? ?]]]].
  try_join h6 h57' h567'; try_join h2 h1457' h12457'; try_join h14' h2 h124'.
  try_join h124' h6 h1246'; try_join_through h1246' h6 h57' h567''; equate_join h567' h567''.
  exists h124', h567', h3, h124567', h3567'; repeat split; auto.
  exists h15', h47', h26, h1457', h2467'; repeat split; auto.
Qed.

(* Lemma exact_frame_ramification {A: Type}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}: *)
(*   forall P Q R R' F, precise P -> (R |-- P * F * TT) -> (F -⊛ R' |-- F -* R') -> ramify R P Q R' -> ramify R (P * F) (Q * F) R'. *)
(* Proof. *)
(*   intros; hnf; intros; specialize (H0 a H3); specialize (H2 a H3). *)
(*   destruct H0 as [y [z [? [[y1 [y2 [? [? ?]]]] ?]]]]; destruct H2 as [y1' [y2z [? [? ?]]]]. *)
(*   try_join y2 z y2z'; equate_precise y1 y1'; equate_canc y2z y2z'. *)
(*   exists y, z; repeat split; auto. exists y1, y2; repeat split; auto. *)
(*   (* clear H5 H. *) *)
(*   replace (((Q * F) -* R')%pred) with ((Q -* (F -* R'))%pred). *)
(*   intros z' m' z'm' ? ? ?. apply H1. *)
(*   (* intros z' m' z'm'; intros; destruct H12 as [m1' [m2' [? [? ?]]]]. *) *)
(*   destruct (nec_join (join_comm H10) H8) as [y2' [y2z' [? [? ?]]]]. *)
(*   (* destruct (nec_join (join_comm H2) H17) as [y1' [a' [? [? ?]]]]. *) *)
(*   destruct (nec_join3 H11 H8) as [m [zm [? [? ?]]]]. *)
(*   destruct (nec_join4 _ _ _ _ H12 H22) as [m1 [m2 [? [? ?]]]]. *)
(*   simpl in H9; hnf in H1; simpl in H1. *)
(*   (* try_join m2' z' m2'z'; specialize (H9 m2'z' m1' z'm'); apply H9; auto. *) *)
(*   specialize (H9 y2z' y1' a' H17 H18). *)
(*   generalize (pred_nec_hereditary _ _ _ H16 H6); intro. *)
(*   admit. *)
(* Qed. *)

Lemma wand_ewand {A: Type}{JA: Join A}{PA: Perm_alg A}{CAA: Canc_alg A}:
  forall R P Q R', precise P -> R |-- P * (Q -* R') -> Q * (P -⊛ R) |-- R'.
Proof.
  intros. intro w. intros. destruct_sepcon H1 h. destruct H3 as [h3 [h4 [? [? ?]]]]. specialize (H0 h4 H5).
  destruct_sepcon H0 h. equate_precise h3 h0. equate_canc h2 h5. apply (H7 h1); auto.
Qed.

Lemma ewand_wand {A: Type}{JA: Join A}{PA: Perm_alg A}{CAA: Canc_alg A}:
  forall R P Q R', R |-- P * TT -> Q * (P -⊛ R) |-- R' -> R |-- P * (Q -* R').
Proof.
  intros. intro w. intros. specialize (H w H1). destruct_sepcon H h. exists h1, h2. do 2 (split; auto). intros w1 w2; intros.
  apply (H0 w2). exists w1, h2. do 2 (split; auto). exists h1, w. split; auto.
Qed.

Definition alignable {A : Type} {JA : Join A} {B : Type} (p : B -> pred A) :=
  forall (x y : B), p x ⊗ p y |-- (p x && !!(x = y)) || ((p x * p y) && !!(x <> y)).

Lemma alignable_emp {A : Type} {JA : Join A} {PA: Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A}: emp ⊗ emp |-- emp.
Proof.
  intro w; intros. destruct_ocon H w. apply (split_identity _ _ (join_comm H0)) in H3.
  apply (join_unit2_e _ _ H3) in H1. subst; auto.
Qed.

Lemma alignable_joinable {A : Type} {JA : Join A} {PA: Perm_alg A} {CA: Cross_alg A} {B : Type}:
  forall (p : B -> pred A) (w : A), alignable p -> joinable p w.
Proof.
  repeat intro. specialize (H x y). assert ((p x ⊗ p y * TT)%pred w). destruct_sepcon H1 w. destruct_sepcon H2 w.
  rename w3 into w4. rename w0 into w3. destruct_cross w. try_join w1 w2w3 wxy. exists wxy, w2w4. do 2 (split; auto).
  exists w1w4, w1w3, w2w3, w1, w3. split; auto. destruct_sepcon H3 w. specialize (H w1 H4). destruct H as [[? ?] | [? ?]].
  exfalso; auto. exists w1, w2. split; auto.
Qed.

Lemma alignable_iter_sepcon {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}
      {C: Cross_alg A} {DA : Disj_alg A} {B : Type}:
  forall (p : B -> pred A) (l : list B) (x : B),
    alignable p -> (forall z, precise (p z)) -> p x ⊗ iter_sepcon l p |--
                                                  (iter_sepcon l p && !!(In x l)) || ((p x * iter_sepcon l p) && !!(~ In x l)).
Proof.
  intros. intro w. intros. destruct_ocon H1 w. try_join w2 w3 w23'; equate_join w23 w23'.
  LEM (In x l); [left | right]; split; auto. apply in_split in H6. destruct H6 as [l1 [l2 ?]]. subst.
  assert (Permutation (l1 ++ x :: l2) (x :: (l2 ++ l1))). rewrite app_comm_cons. apply Permutation_app_comm.
  generalize (iter_sepcon_permutation _ _ p H6); intro. rewrite H8 in *. clear H6 H8. simpl in H5. destruct_sepcon H5 h.
  destruct_cross w23. assertSub w12 w HS1. assertSub h1 w HS2. generalize (H0 x); intro. equate_precise_through (p x) w12 h1.
  clear H13. assert (emp w1). apply join_sub_joins_identity with w23. try_join w1 h2 t1. assertSub w1 w23 HS. auto.
  exists w. auto. elim_emp. simpl. exists w12, h2. split; auto.

  clear H7. revert w w1 w2 w3 w12 w23 H1 H2 H3 H4 H5 H6.
  induction l; intros; simpl in *; try_join w2 w3 w23'; equate_join w23 w23'. rewrite sepcon_emp. apply join_comm in H2.
  apply split_identity in H2; auto. elim_emp. auto. assert (a <> x). intro. apply H6. left; auto. assert (~ In x l). intro.
  apply H6. right; auto. clear H6. destruct_sepcon H5 h. destruct_cross w23. rename w2h1 into i1. rename w3h1 into i2.
  rename w2h2 into i4. rename w3h2 into i3. try_join w1 i4 w1i4. try_join h1 i4 h1i4. try_join w12 i2 w12h1.
  assert ((p x ⊗ p a)%pred w12h1). exists w1i4, i1, i2, w12, h1. split; auto. apply H in H21. destruct H21 as [[? ?] | [? ?]].
  exfalso; auto. assert (emp i1). apply (overlapping_precise_emp w1i4 i1 i2 w12 h1 w12h1 (p x) (p a)); auto. elim_emp.
  clear H23 i1. try_join h2 w1 w1h2. rewrite <- sepcon_assoc. rewrite (sepcon_comm (p x)). rewrite sepcon_assoc.
  exists h1, w1h2. do 2 (split; auto). try_join w12 i3 w1h2'. equate_canc w1h2 w1h2'. apply (IHl _ w1 w2 i3 w12 h2); auto.
Qed.

Lemma disjoint_iter_sepcon_app {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A} {C: Cross_alg A}
      {DA : Disj_alg A} {B : Type}:
  forall (p : B -> pred A) (l1 l2 : list B), alignable p -> (forall z, precise (p z)) -> (forall x, In x l1 -> ~ In x l2) ->
                                             iter_sepcon l1 p ⊗ iter_sepcon l2 p |-- iter_sepcon l1 p * iter_sepcon l2 p.
Proof.
  intros. induction l1; intro w; intros. simpl in *. rewrite ocon_comm, ocon_emp in H2. rewrite sepcon_comm, sepcon_emp. auto.
  simpl in *. destruct_ocon H2 w. destruct_sepcon H5 h. destruct_cross w12. rename w1h1 into i1. rename w2h1 into i2.
  rename w1h2 into i3. rename w2h2 into i4. try_join w2 w3 w23'; equate_join w23 w23'. try_join i4 w3 i4w3.
  try_join w23 i1 w23h1. try_join i1 i2 h1'. equate_join h1 h1'. assert ((p a ⊗ iter_sepcon l2 p)%pred w23h1).
  exists i1, i2, i4w3, h1, w23. split; auto. apply alignable_iter_sepcon in H18; auto. destruct H18 as [[? ?] | [? ?]].
  simpl in H20. exfalso. specialize (H1 a). apply H1; [left|]; auto. assert (emp i2).
  apply (overlapping_precise_emp i1 i2 i4w3 h1 w23 w23h1 (p a) (iter_sepcon l2 p)); auto. apply precise_iter_sepcon. auto.
  elim_emp. clear H21 i2. try_join h2 w3 h2w3. rewrite sepcon_assoc. exists h1, h2w3. do 2 (split; auto). apply IHl1. intros.
  apply H1. right; auto. exists i3, w2, w3, h2, w23. split; auto.
Qed.

(* Lemma alignable_unique {A : Type} {JA : Join A} {PA: Perm_alg A} {SA : Sep_alg A} {B : Type}: *)
(*   forall (p : B -> pred A), alignable p -> sepcon_unique p. *)
(* Proof. *)
(*   intros. intros x w. intro. destruct_sepcon H0 w. assert ((p x ⊗ p x)%pred w). remember (core w) as cw. *)
(*   exists w1, cw, w2, w1, w2. split. apply join_core in H0. subst. rewrite <- H0. apply join_comm, core_unit. split. *)
(*   apply join_comm in H0. apply join_core in H0. subst. rewrite <- H0. apply core_unit. split; auto. specialize (H x x w H3). *)
(*   destruct H as [[? ?] | [? ?]]. clear H3 H4. admit. intuition. *)
(* Qed. *)

