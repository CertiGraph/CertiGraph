Require Import msl.msl_direct.
Require Import FunctionalExtensionality.

Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
Proof. constructor; intros; inv H. Qed.

Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
Proof. repeat intro. inv H. Qed.

Definition table (A B : Type) := list (A*B).

Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
    | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
    | nil => None
  end.

Definition table_set {A B}{H: EqDec A} (x: A) (v: B) (rho: table A B)  : table A B := (x,v)::rho.

Lemma table_gss {A B}{H: EqDec A}: forall rho x (v: B), table_get (table_set x v rho) x = Some v.
Proof.
  intros.
  simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A B}{H: EqDec A}: forall rho x y (v:B), x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
  intros.
  simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.

Definition var := nat.
Definition adr := nat.
Definition stack := table var adr.
Definition heap := table adr adr.
Definition state := (stack * heap)%type.

Definition world := ((var -> option adr)*(adr -> option adr))%type.

Instance Join_world: Join world :=
  Join_prod
    (var -> option adr) (Join_equiv _)
    (adr -> option adr) (Join_fun adr (option adr) (Join_lower (Join_discrete adr))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.

Instance Canc_world : Canc_alg world.
apply Canc_prod; [apply Canc_equiv | apply Canc_fun, Canc_lower; [intuition | repeat intro; inversion H]].
Qed.

Instance Disj_world : Disj_alg world.
apply Disj_prod; [apply Disj_equiv | apply Disj_fun, Disj_lower; repeat intro; inversion H].
Qed.

Instance Cross_opt_adr : @Cross_alg (option adr) (@Join_lower adr (Join_discrete adr)).
repeat intro.
assert (X : @Cross_alg adr (Join_discrete adr)) by (repeat intro; inv H1).
icase a; icase b; icase z; icase c; icase d;
let Heq := fresh "Heq" in
repeat match goal with
         | [H : join (Some _) (Some _) None |- _] => exfalso; inv H
         | [H : join (Some _) None None |- _] => exfalso; inv H
         | [H : join None None (Some _) |- _] => exfalso; inv H
         | [H : join None (Some _) None |- _] => exfalso; inv H
         | [H : join (Some ?Xa) (Some ?Ya) (Some ?Za) |- _] => assert (join Xa Ya Za) by (inv H; trivial); clear H
         | [H : join (Some ?Xa) None (Some ?Ya) |- _] =>
           assert (Heq: Xa = Ya) by (inv H; trivial); clear H; rewrite Heq in *; clear Heq Xa
         | [H : join None (Some ?Xa) (Some ?Ya) |- _] =>
           assert (Heq: Xa = Ya) by (inv H; trivial); clear H; rewrite Heq in *; clear Heq Xa
       end.
Ltac solve_lower :=
  repeat split;
  match goal with
    | [|- join (Some ?Xa) None (Some ?Xa)] => apply lower_None2
    | [|- join None (Some ?Xa) (Some ?Xa)] => apply lower_None1
    | [|- join None None None] => apply lower_None1
    | [H: join ?Xa ?Ya ?Za |- join (Some ?Xa) (Some ?Ya) (Some ?Za)] => apply lower_Some; apply H
  end.
destruct (X a a0 a2 a3 a1 H0 H1) as [[[[ac ad] bc] bd] [? [? [? ?]]]];
  exists (Some ac, Some ad, Some bc, Some bd); solve_lower.
exists (Some a, None, Some a0, None); solve_lower.
exists (None, Some a, None, Some a0); solve_lower.
exists (Some a1, Some a2, None, None); solve_lower.
exists (Some a0, None, None, None); solve_lower.
exists (None, Some a0, None, None); solve_lower.
exists (None, None, Some a1, Some a2); solve_lower.
exists (None, None, Some a0, None); solve_lower.
exists (None, None, None, Some a0); solve_lower.
exists (None, None, None, None); solve_lower.
Qed.

Instance Cross_world : Cross_alg world.
apply Cross_prod.
apply Cross_equiv.
repeat intro.
pose (f (x: adr) := projT1 (Cross_opt_adr (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (g (x: adr) := projT2 (Cross_opt_adr (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (ac (x: adr) := fst (fst (fst (f x)))).
pose (ad (x: adr) := snd (fst (fst (f x)))).
pose (bc (x: adr) := snd (fst (f x))).
pose (bd (x: adr) := snd (f x)).
exists (ac,ad,bc,bd); unfold ac, ad, bc, bd, f; clear ac ad bc bd f.
repeat split; intro x; simpl; generalize (g x);
destruct (projT1 (Cross_opt_adr (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))) as [[[? ?] ?] ?]; simpl; intuition.
Qed.

Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) :=
  fun i => if eq_dec i x then y else f i.

Definition subst (x y: var) (P: pred world) : pred world :=
  fun w => P (fun_set (fst w) x (fst w y), snd w). 

Definition mapsto (x y: var) : pred world :=
  fun w => x <> 0 /\
    exists ax, fst w x = Some ax /\
               exists ay, fst w y = Some ay /\
                          (forall a, a <> ax -> snd w a = None) /\ snd w ax = Some ay.

Lemma precise_mapsto: forall x y, precise(mapsto x y).
Proof.
  repeat intro; destruct w1 as [r1 m1]; destruct w2 as [r2 m2]; destruct w as [r m].
  destruct H1 as [[rx mx] [[? ?] ?]]; destruct H2 as [[ry my] [[? ?] ?]]; simpl in H1, H2, H3, H4, H5, H6.
  assert (r1 = r2) by (rewrite H1 in *; rewrite H3 in *; rewrite H2 in *; rewrite H5 in *; trivial); clear H1 H2 H3 H5 rx ry r.
  destruct H as [? [ax1 [? [ay1 [? [? ?]]]]]]; simpl in H1, H2, H3, H5.
  destruct H0 as [? [ax2 [? [ay2 [? [? ?]]]]]]; simpl in H8, H9, H10, H11.
  rewrite H7 in *; clear H7 r1. rewrite H1 in H8; inversion H8. rewrite H12 in *; clear H12 ax1.
  rewrite H2 in H9; inversion H9; rewrite H12 in *; clear H12 ay1.
  assert (m1 = m2). extensionality mm; destruct (eq_dec mm ax2).
  rewrite e in *; rewrite H5, H11; trivial.
  specialize(H3 mm n); specialize (H10 mm n); rewrite H3, H10; trivial.
  repeat f_equal; trivial.
Qed.

Definition equal (x y: var) : pred world := fun w => fst w x = fst w y.
