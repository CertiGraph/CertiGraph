Require Import msl.msl_direct.

Ltac destruct_ocon H h :=
  let h1 := fresh h "1" in
  let h2 := fresh h "2" in
  let h3 := fresh h "3" in
  let h12 := fresh h "12" in
  let h23 := fresh h "23" in
  destruct H as [h1 [h2 [h3 [h12 [h23 [? [? [? [? ?]]]]]]]]].

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
