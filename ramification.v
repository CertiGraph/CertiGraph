Require Import msl.msl_classical.
Require Import overlapping.

Definition ramify {A: Type}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A}
           (R P Q R' : pred A) := R |-- P * (Q -* R').

Ltac assertSub a c Hsub :=
  match goal with
    | [_: join a ?b c |- _] => assert (Hsub: join_sub a c) by (exists b; auto)
    | [H: join ?b a c |- _] => assert (Hsub: join_sub a c) by (exists b; apply join_comm; auto)
  end.

Ltac equate_precise x1 x2 :=
  let Sub1 := fresh "Sub1" in
  let Sub2 := fresh "Sub2" in
  let Heq := fresh "Heq" in
  match goal with
    | [_ : join x1 _ ?c, _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c, _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join x1 _ ?c, _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c, _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
  end;
  match goal with
    | [H1: precise _, H2: ?P x1, H3: ?P x2, H4: join_sub x1 ?w, H5: join_sub x2 ?w |- _] =>
      generalize (H1 w x2 x1 H3 H2 H5 H4); intro Heq;
      rewrite Heq in *; clear H3 H4 H5 Heq x2
  end.

Ltac equate_canc x1 x2 :=
  let Heq := fresh "Heq" in
  let helper M1 M2 M3 := generalize (join_canc M2 M1); intro Heq; rewrite Heq in *; clear M3 Heq x2 in
    match goal with
      | [H1: join x1 ?b ?c, H2: join x2 ?b ?c |- _] => helper H1 H2 H2
      | [H1: join ?b x1 ?c, H2: join x2 ?b ?c |- _] => helper (join_comm H1) H2 H2
      | [H1: join x1 ?b ?c, H2: join ?b x2 ?c |- _] => helper H1 (join_comm H2) H2
      | [H1: join ?b x1 ?c, H2: join ?b x2 ?c |- _] => helper (join_comm H1) (join_comm H2) H2
    end.

Lemma overlapping_ramification {A: Type}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q R R' F, precise P -> precise Q -> ramify (P ⊗ R) P Q (Q ⊗ R') ->
                     ramify ((P * F) ⊗ R) P Q ((Q * F) ⊗ R').
Proof.
  intros; hnf; intros; simpl in H2;
  destruct H2 as [h1 [h2 [h3 [h12 [h23 [? [? [? [[y [z [? [HPy HFz]]]] HR23]]]]]]]]];
  destruct (cross_split h1 h2 y z h12 H2 H5) as [[[[h1y h1z] h2y] h2z] [? [? [? ?]]]].
  try_join h1y h2 h1y2; try_join h1y2 h3 h1y23; try_join h1y h2y y'; equate_join y y'.
  try_join h2z h3 h2z3; try_join_through h1y2 h2z h3 h2z3'; equate_join h2z3 h2z3';
  assert (HPR: (P ⊗ R)%pred h1y23) by (simpl; exists h1y, h2y, h2z3, y, h23; split; auto);
  specialize (H1 h1y23 HPR); destruct H1 as [y' [h2z3' [? [HPy' HPQ]]]]; equate_precise y y';
  equate_canc h2z3 h2z3'; try_join z h3 hz3; exists y, hz3; repeat split; auto;
  intros hz3' m hz3'm HnecRz3 ? HQm; destruct (nec_join2 H1 HnecRz3) as [z' [h3' [? [HnecRz HnecR3]]]];
  assert (HFz': F z') by (apply pred_nec_hereditary with z; auto).
  try_join h2z h3 h2z3'; equate_join h2z3 h2z3';
  destruct (nec_join2 H22 HnecRz3) as [h1z' [h2z3' [? [HnecR1z' HnecR2z3']]]]; try_join h2z3' m h2z3'm;
  assert (HQR': (Q ⊗ R')%pred h2z3'm) by (apply HPQ with (x' := h2z3')(y := m); auto);
  destruct HQR' as [m1 [m2 [h2z3'' [m' [hm22z3' [? [? [? [HQm' HR']]]]]]]]]; equate_precise m m'; equate_canc h2z3' h2z3'';
  destruct (nec_join2 H14 HnecR2z3') as [h2z' [h3'' [? [HnecR2z' HnecR3'']]]];
  assert (Heq: h3'' = h3') by (apply @necR_linear' with (a := h3)(H := AG); auto;
                               apply join_level in H27; destruct H27 as [? Heq1]; rewrite Heq1;
                               apply join_level in H21; destruct H21 as [? Heq2]; rewrite Heq2;
                               apply join_level in H20; destruct H20 as [? Heq3]; auto); rewrite Heq in *;
  clear Heq HnecR3'' h3''; try_join h1z' h2z' z''; equate_canc z' z'';
  try_join h2z' m2 m22z'; try_join z' m hz'm; try_join m1 z' hz'm1; try_join h1z' m1 m11z';
  exists m11z', m22z', h3', hz'm, hm22z3'; repeat split; auto;
  [try_join h2z' m2 m22z''; equate_join m22z' m22z''| exists m, z'; split]; auto.
Qed.

Lemma andp_ramification1 {A: Type}{JA: Join A}{PA: Perm_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q R R' F, precise P -> ramify R P Q R' -> ramify ((P * F) && R) P Q ((Q * F) && R').
Proof.
  intros; hnf; intros; destruct H1 as [[y [z [? [? ?]]]] ?].
  specialize (H0 a H4); destruct H0 as [y' [z' [? [? ?]]]]; equate_precise y y'; equate_canc z z'.
  exists y, z; do 2 (split; auto); intros z' m z'm; intros; specialize (H6 z' m z'm H0 H5 H7).
  split; auto; exists m, z'; repeat split; auto; apply pred_nec_hereditary with z; auto.
Qed.

Notation "P '-⊛' Q" := (ewand P Q) (at level 60, right associativity) : pred.

Lemma andp_ramification2 {A: Type}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}:
  forall P Q R R' F, (P -⊛ R |-- Q -* R') -> ramify ((P * F) && R) P Q ((Q * F) && R').
Proof.
  intros; hnf; intros; destruct H0 as [[y [z [? [? ?]]]] ?].
  assert ((P -⊛ R)%pred z) by (exists y, a; repeat split; auto).
  specialize (H z H4); exists y, z; do 2 (split; auto).
  intros z' m z'm; intros; specialize (H z' m z'm H5 H6 H7).
  split; auto; exists m, z'; repeat split; auto; apply pred_nec_hereditary with z; auto.
Qed.

(* Lemma exact_frame_ramification {A: Type}{JA: Join A}{PA: Perm_alg A}{CA: Cross_alg A}{CAA: Canc_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A}: *)
(*   forall P Q R R' F, precise P -> (R |-- P * F * TT) ->  *)

