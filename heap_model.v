Require Import msl.msl_classical.

  Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

  Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
  Proof. constructor; intros; inv H.
  Qed.

  Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
  Proof.
    repeat intro. inv H.
  Qed.


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
  fun w =>
    exists ax, fst (snd w) x = Some ax /\
               exists ay, fst (snd w) y = Some ay /\
                          forall a, if eq_dec a ax then snd (snd w) a = Some ay else snd (snd w) a = None.
Next Obligation.
  intros. intro; intros.
  unfold age in H;  destruct a; destruct a'; simpl in H. destruct n; inv H.
  simpl in *. auto.
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
