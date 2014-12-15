Require Import msl.msl_direct.
Require Import FunctionalExtensionality.
Require Import ramify_tactics.

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

Definition world := (fpm adr adr).

Instance Join_world: Join world := Join_fpm (Join_discrete adr).

Instance Perm_world : Perm_alg world.
apply Perm_fpm; apply Perm_discrete.
Qed.

Instance Sep_world : Sep_alg world.
apply Sep_fpm.
Qed.

Instance Canc_world : Canc_alg world.
apply Canc_fpm; [intuition | repeat intro; inversion H].
Qed.

Instance Disj_world : Disj_alg world.
apply Disj_fpm; repeat intro; inversion H.
Qed.

Instance Cross_world : Cross_alg world.
apply Cross_fpm; [apply Perm_discrete | apply psa_discrete | repeat intro; inv H].
Qed.

(* Definition fun_set (f: nat -> option nat) (x: nat) (y: option nat) := *)
(*   fun i => if eq_dec i x then y else f i. *)

(* Definition subst (x y: var) (P: pred world) : pred world := *)
(*   fun w => P (fun_set (fst w) x (fst w y), snd w). *)

Definition mapsto (x y: adr) : pred world :=
  fun w => x <> 0 /\
    (forall a, a <> x -> lookup_fpm w a = None) /\
    lookup_fpm w x = Some y.

Lemma join_sub_mapsto: forall w1 w2 x y, join_sub w1 w2 -> (mapsto x y * TT)%pred w1 -> (mapsto x y * TT)%pred w2.
Proof.
  intros. destruct_sepcon H0 h. destruct H as [w3 ?]. try_join h2 w3 m. exists h1, m. split; auto.
Qed.

Lemma precise_mapsto: forall x y, precise (mapsto x y).
Proof.
  repeat intro. clear H1 H2 w. destruct H0 as [? [? ?]]. destruct H as [? [? ?]].
  destruct w1 as [x1 f1]; destruct w2 as [x2 f2]; simpl in *.
  apply exist_ext. extensionality mm; destruct (eq_dec mm x).
  rewrite e in *. rewrite H4, H2; trivial.
  specialize (H1 mm n); specialize (H3 mm n); rewrite H1, H3; trivial.
Qed.

Fixpoint extractSome (f : adr -> option adr) (li : list adr) : list adr :=
  match li with
    | nil => nil
    | x :: lx => match f x with
                   | Some _ => x :: extractSome f lx
                   | None => extractSome f lx
                 end
  end.

Lemma world_finite: forall w: world, exists l: list adr, forall a:adr, In a l <-> lookup_fpm w a <> None.
Proof.
  intro; destruct w as [f [li ?]]; simpl; exists (extractSome f li); split; intros.
  clear e; induction li; simpl in H; auto.
  destruct (f a0) eqn: ?. destruct (in_inv H). subst. rewrite Heqo. intro. inversion H0.
  apply IHli; auto. apply IHli; auto. destruct (in_dec nat_eq_dec a li). clear e.
  induction li; simpl in *; auto. destruct (f a0) eqn : ?. destruct i. subst. apply in_eq.
  apply in_cons. apply IHli; auto. destruct i. subst. exfalso; auto. apply IHli; auto.
  specialize (e a n). exfalso; auto.
Qed.

Lemma lookup_fpm_join_sub: forall (w1 w2 : world) x, join_sub w1 w2 -> lookup_fpm w1 x <> None -> lookup_fpm w2 x <> None.
Proof.
  intros. destruct H as [w3 ?].
  destruct w1 as [f1 [l1 ?]]. destruct w2 as [f2 [l2 ?]]. destruct w3 as [f3 [l3 ?]]. hnf in H; simpl in *.
  specialize (H x). inversion H. exfalso; auto. auto. auto.
Qed.

(* Definition equal (x y: var) : pred world := fun w => fst w x = fst w y. *)
