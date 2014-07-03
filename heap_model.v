Require Import msl.msl_classical.
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

Definition world := (nat * ((var -> option adr)*(adr -> option adr)))%type.

Instance Join_world: Join world :=
  Join_prod nat (Join_equiv nat)
            _
            (Join_prod
               (var -> option adr) (Join_equiv _)
               (adr -> option adr) (Join_fun adr (option adr) (Join_lower (Join_discrete adr)))).

Instance Perm_world : Perm_alg world := _.
Instance Sep_world : Sep_alg world := _.
Instance Canc_world : Canc_alg world.
apply Canc_prod; [apply Canc_equiv |
                  apply Canc_prod; [apply Canc_equiv | apply Canc_fun, Canc_lower; [intuition | repeat intro; inversion H]]].
Defined.
Instance Disj_world : Disj_alg world.
apply Disj_prod; [apply Disj_equiv |
                  apply Disj_prod; [apply Disj_equiv | apply Disj_fun, Disj_lower; repeat intro; inversion H]].
Defined.

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
Defined.

Instance Cross_world : Cross_alg world.
apply Cross_prod.
apply Cross_equiv.
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
Defined.

Definition age_world (w: world) : option world :=
  match fst w with S n => Some (n, snd w) | O => None end.

Definition level_world (w: world) : nat := fst w.

Lemma af_world: ageable_facts _ level_world age_world.
Proof.
  constructor.
  intros [n x]; exists (S n, x); simpl; auto.
  intros [n x]; unfold age_world; destruct n; simpl; intuition discriminate.
  intros. destruct x as [n x]; destruct n; inv H; simpl; auto.
Qed.

Instance ag_world: ageable world := mkAgeable _ _ _ af_world.
Instance Age_world : Age_alg world.
constructor.
intros [nx x] [ny y] [nz z] [nx' x'] [? ?] ?; simpl in *. destruct H; subst.
unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
exists (nx', y); exists (nx', z); split; auto; split; auto.
intros [nx x] [ny y] [nz z] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
exists (nz', x); exists (nz', y); split; auto; split; auto.
intros [nx x] [nx' x'] [ny' y'] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
destruct nx; inv H1. unfold age; simpl. unfold age_world; simpl.
exists (S nz', y'); exists (S nz', z'); split; auto; split; auto.
intros [nz z] [nx' x'] [ny' y'] [nz' z'] [? ?] ?; simpl in *. destruct H; subst.
unfold age in H1. simpl in H1. unfold age_world in H1. simpl in H1.
destruct nz; inv H1. unfold age; simpl. unfold age_world; simpl.
exists (S nz', x'); exists (S nz', y'); split; auto; split; auto.
Qed.

Definition den (lev: nat) (s: state) : world := (lev, (table_get (fst s), table_get (snd s))).

Obligation Tactic := (try solve [repeat intro; match goal with H: age _ _ |- _ => inv H end]).

Program Definition defined (y: var) : pred world :=
  fun w => exists v, fst (snd w) y = Some v.
Next Obligation.
  intros. intro; intros.
  unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
  auto.
Qed.

Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) :=
  fun i => if eq_dec i x then y else f i.

Program Definition subst (x y: var) (P: pred world) : pred world :=
  fun w => P (fst w, (fun_set (fst (snd w)) x (fst (snd w) y), snd (snd w))).
Next Obligation.
  intros. intro; intros.
  unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
  simpl in *. eapply pred_hereditary; eauto.
  unfold age; simpl. unfold age_world; simpl. auto.
Qed.

Program Definition mapsto (x y: var) : pred world :=
  fun w => x <> 0 /\
    exists ax, fst (snd w) x = Some ax /\
               exists ay, fst (snd w) y = Some ay /\
                          (forall a, a <> ax -> snd (snd w) a = None) /\ snd (snd w) ax = Some ay.
                          (* forall a, if eq_dec a ax then snd (snd w) a = Some ay else snd (snd w) a = None. *)
Next Obligation.
  intros. intro; intros. destruct H0.
  split; auto.
  unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
  simpl in *. auto.
Qed.

Lemma precise_mapsto: forall x y, precise(mapsto x y).
Proof.
  repeat intro; destruct w1 as [n1 [rho1 m1]]; destruct w2 as [n2 [rho2 m2]]; destruct w as [n [rho m]];
  destruct H1; destruct x0 as [nx [rhox mx]]; destruct H1; destruct H1;
  destruct H2; destruct x0 as [ny [rhoy my]]; destruct H2; destruct H2; simpl in H1, H2, H3, H4, H5, H6.
  assert (n1 = n2). rewrite H1 in *; rewrite H4 in *; rewrite H2 in *; rewrite H6 in *; trivial. clear H1 H2 H4 H6 nx ny n.
  destruct H3, H5; destruct H1, H3; simpl in H1, H2, H3, H4, H5, H6.
  assert (rho1 = rho2). rewrite H1 in *; rewrite H5 in *; rewrite H3 in *; rewrite H6 in *; trivial.
  clear H1 H5 H3 H6 rhox rhoy rho.
  destruct H as [? [ax1 [? [ay1 [? ?]]]]]; simpl in H1, H3, H5; destruct H0 as [? [ax2 [? [ay2 [? ?]]]]]. simpl in H6, H9, H10.
  rewrite H8 in * |-. rewrite H1 in H6. injection H6; intro. rewrite H11 in *.
  rewrite H3 in H9; injection H9; intro; rewrite H12 in *. destruct H5, H10.
  assert (m1 = m2).
  extensionality mm; destruct (eq_dec mm ax2);
  [rewrite e in *; rewrite H13, H14; auto | specialize (H5 mm n); specialize (H10 mm n); rewrite H5, H10; auto].
  repeat f_equal; trivial.
Qed.

Program Definition equal (x y: var) : pred world :=
  fun w => fst (snd w) x = fst (snd w) y.
Next Obligation.
  intros. intro; intros.
  unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
  simpl in *. auto.
Qed.

Definition nonfreevars (P: pred world) (x: var) : Prop :=
  forall lev stk hp v, P (lev, (stk,hp)) -> P (lev, (fun_set stk x v, hp)).

Definition subset (S1 S2: var -> Prop) :=
  forall x, S1 x -> S2 x.
