Require Import VST.msl.msl_standard.

Ltac equate_age a1 a2 :=
  let Heq := fresh "Heq" in
  let Heq1 := fresh "Heq1" in
  let Heq2 := fresh "Heq2" in
  match goal with
    | [H1: age ?X a1, H2: age ?X a2 |- _] =>
      assert (Heq1: age1 X = Some a1) by auto; assert (Heq2: age1 X = Some a2) by auto;
      rewrite Heq2 in Heq1; injection Heq1; intro Heq; rewrite Heq in *; clear Heq1 Heq2 H2 Heq
  end.

Ltac destruct_ocon H h :=
  let h1 := fresh h "1" in
  let h2 := fresh h "2" in
  let h3 := fresh h "3" in
  let h12 := fresh h "12" in
  let h23 := fresh h "23" in
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].

Ltac destruct_sepcon H h :=
  let h1 := fresh h "1" in
  let h2 := fresh h "2" in
  destruct H as [h1 [h2 [? [? ?]]]].

Ltac destruct_cross h :=
  match goal with
    | [H1: join ?h1 ?h2 h, H2: join ?x1 ?x2 h |- _] =>
      let h1x1 := fresh h1 x1 in
      let h1x2 := fresh h1 x2 in
      let h2x1 := fresh h2 x1 in
      let h2x2 := fresh h2 x2 in
      destruct (cross_split h1 h2 x1 x2 h H1 H2) as [[[[h1x1 h1x2] h2x1] h2x2] [? [? [? ?]]]]
  end.

Ltac try_join h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join ?X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ ?X, H2: join m2 ?X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac try_join_through X h1 h2 h1h2 :=
  let helper m1 m2 m1m2 :=
      match goal with
        | [H1: join _ m1 X, H2: join X m2 _ |- _] => destruct (join_assoc H1 H2) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join X m2 _ |- _] => destruct (join_assoc (join_comm H1) H2) as [m1m2 [? ?]]
        | [H1: join _ m1 X, H2: join m2 X _ |- _] => destruct (join_assoc H1 (join_comm H2)) as [m1m2 [? ?]]
        | [H1: join m1 _ X, H2: join m2 X _ |- _] => destruct (join_assoc (join_comm H1) (join_comm H2)) as [m1m2 [? ?]]
      end
  in helper h1 h2 h1h2 || helper h2 h1 h1h2.

Ltac equate_join x1 x2 :=
  let Heq := fresh "Heq" in
  match goal with
    |[H1: join ?a ?b x1, H2: join ?b ?a x2 |- _] => apply join_comm in H2
    | _ => idtac
  end;
  match goal with
    |[H1: join ?a ?b x1, H2: join ?a ?b x2 |- _] =>
     generalize (join_eq H2 H1); intro Heq;
     rewrite Heq in *; clear H2 Heq x2
  end.

Ltac assertSub a c Hsub :=
  match goal with
    | [H: join a _ c |- _] => assert (Hsub: join_sub a c) by (apply join_join_sub in H; auto)
    | [H: join _ a c |- _] => assert (Hsub: join_sub a c) by (apply join_join_sub' in H; auto)
    | [H1: join_sub a ?x, H2: join_sub ?x c |- _] => assert (Hsub: join_sub a c) by (apply join_sub_trans with (b := x); auto)
    | [H1: join _ a ?x, H2: join_sub ?x c |- _] => let H := fresh "H" in assertSub a x H; assertSub a c Hsub; clear H
    | [H1: join a _ ?x, H2: join_sub ?x c |- _] => let H := fresh "H" in assertSub a x H; assertSub a c Hsub; clear H
    | [H1: join a _ ?x, H2: join ?x _ c |- _] => let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join a _ ?x, H2: join _ ?x c |- _] => let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join _ a ?x, H2: join ?x _ c |- _] => let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join _ a ?x, H2: join _ ?x c |- _] => let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join a _ ?x, H2: join ?x _ ?y, H3: join_sub ?y c |- _] =>
      let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join a _ ?x, H2: join _ ?x ?y, H3: join_sub ?y c |- _] =>
      let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join _ a ?x, H2: join ?x _ ?y, H3: join_sub ?y c |- _] =>
      let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
    | [H1: join _ a ?x, H2: join _ ?x ?y, H3: join_sub ?y c |- _] =>
      let H := fresh "H" in assertSub x c H; assertSub a c Hsub; clear H
  end.

(* For standard precise *)
Ltac equate_precise x1 x2 :=
  let Sub1 := fresh "Sub1" in
  let Sub2 := fresh "Sub2" in
  let Heq := fresh "Heq" in
  match goal with
    | [_ : join x1 _ ?c,   _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c,   _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join_sub x1 ?c, _: join x2 _ ?c |- _] => assertSub x2 c Sub2
    | [_ : join x1 _ ?c,   _: join_sub x2 ?c |- _] => assertSub x1 c Sub1
    | [_ : join _ x1 ?c,   _: join_sub x2 ?c |- _] => assertSub x1 c Sub1 
    | [_ : join_sub x1 ?c, _: join_sub x2 ?c |- _] => idtac 
    | [_ : join x1 _ ?c,   _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c,   _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join_sub x1 ?c, _: join _ x2 ?c |- _] => assertSub x2 c Sub2
  end;
  match goal with
    | [H1: precise _, H2: ?P x1, H3: ?P x2, H4: join_sub x1 ?w, H5: join_sub x2 ?w |- _] =>
      generalize (H1 w x2 x1 H3 H2 H5 H4); intro Heq;
      rewrite Heq in *; clear H3 H4 H5 Heq x2
  end.

(* Ltac equate_precise_through P x1 x2 := *)
(*   match goal with *)
(*     | [H1: precise P, H2: P x1, H3: P x2, H4: join_sub x1 ?w, H5: join_sub x2 ?w |- _] => *)
(*       generalize (H1 w x2 x1 H3 H2 H5 H4); intro Heq; *)
(*       rewrite Heq in *; clear H3 H4 H5 Heq x2 *)
(*   end. *)

Ltac equate_canc x1 x2 :=
  let Heq := fresh "Heq" in
  let helper M1 M2 M3 := generalize (join_canc M2 M1); intro Heq; rewrite Heq in *; clear M3 Heq x2 in
    match goal with
      | [H1: join x1 ?b ?c, H2: join x2 ?b ?c |- _] => helper H1 H2 H2
      | [H1: join ?b x1 ?c, H2: join x2 ?b ?c |- _] => helper (join_comm H1) H2 H2
      | [H1: join x1 ?b ?c, H2: join ?b x2 ?c |- _] => helper H1 (join_comm H2) H2
      | [H1: join ?b x1 ?c, H2: join ?b x2 ?c |- _] => helper (join_comm H1) (join_comm H2) H2
    end.

Ltac elim_emp :=
  repeat match goal with
           | [H1: join ?x ?y _, H2: emp ?x |- _] => apply (join_unit1_e _ _ H2) in H1; rewrite H1 in *; clear H1 y
           | [H1: join ?y ?x _, H2: emp ?x |- _] => apply (join_unit2_e _ _ H2) in H1; rewrite H1 in *; clear H1 y
         end.

Require Import VST.msl.msl_direct.

(* For direct precise *)

Ltac equate_precise_direct x1 x2 :=
  let Sub1 := fresh "Sub1" in
  let Sub2 := fresh "Sub2" in
  let Heq := fresh "Heq" in
  match goal with
    | [_ : join x1 _ ?c,   _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c,   _: join x2 _ ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join_sub x1 ?c, _: join x2 _ ?c |- _] => assertSub x2 c Sub2
    | [_ : join x1 _ ?c,   _: join_sub x2 ?c |- _] => assertSub x1 c Sub1
    | [_ : join _ x1 ?c,   _: join_sub x2 ?c |- _] => assertSub x1 c Sub1 
    | [_ : join_sub x1 ?c, _: join_sub x2 ?c |- _] => idtac 
    | [_ : join x1 _ ?c,   _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join _ x1 ?c,   _: join _ x2 ?c |- _] => assertSub x1 c Sub1; assertSub x2 c Sub2
    | [_ : join_sub x1 ?c, _: join _ x2 ?c |- _] => assertSub x2 c Sub2
  end;
  match goal with
    | [H1: precise _, H2: ?P x1, H3: ?P x2, H4: join_sub x1 ?w, H5: join_sub x2 ?w |- _] =>
      generalize (H1 w x2 x1 H3 H2 H5 H4); intro Heq;
      rewrite Heq in *; clear H3 H4 H5 Heq x2
  end.

Ltac elim_emp_direct :=
  repeat match goal with
           | [H1: join ?x ?y _, H2: emp ?x |- _] => apply (join_unit1_e _ _ H2) in H1; rewrite H1 in *; clear H1 y
           | [H1: join ?y ?x _, H2: emp ?x |- _] => apply (join_unit2_e _ _ H2) in H1; rewrite H1 in *; clear H1 y
         end.
