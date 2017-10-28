Require Import VST.msl.msl_direct.
Require Import RamifyCoq.msl_ext.abs_addr.

Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
Proof. constructor; intros; inv H. Qed.

Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
Proof. repeat intro. inv H. Qed.

(* Definition var := nat. *)
Definition adr := nat.

Definition world := (fpm adr adr).

Instance Join_world: Join world := Join_fpm (Join_discrete adr).

Instance Perm_world : Perm_alg world. apply Perm_fpm; apply Perm_discrete. Qed.

Instance Sep_world : Sep_alg world. apply Sep_fpm. Qed.

Instance Canc_world : Canc_alg world. apply Canc_fpm; [intuition | repeat intro; inversion H]. Qed.

Instance Disj_world : Disj_alg world. apply Disj_fpm; repeat intro; [apply Perm_discrete | |]; inversion H. Qed.

Instance Cross_world : Cross_alg world. apply Cross_fpm; [apply Perm_discrete | apply psa_discrete | repeat intro; inv H]. Qed.

Instance Trip_world : @Trip_alg world Join_world.
Proof.
  repeat intro.
  destruct ab as [fab Hab]. destruct c as [fc Hc].
  remember (fun x => match (fab x) with
                       | Some v => Some v
                       | None => match (fc x) with
                                   | Some v' => Some v'
                                   | None => None
                                 end
                     end) as fabc.
  assert (finMap fabc). {
    hnf in Hab, Hc. destruct Hab as [lab ?]. destruct Hc as [lc ?].
    exists (lab ++ lc). intro z; intros.
    assert (~ In z lab). intro. apply H2. apply in_or_app. left; auto.
    assert (~ In z lc). intro. apply H2. apply in_or_app. right; auto.
    hnf in *. simpl in *. specialize (e0 z H4). specialize (e z H3).
    rewrite Heqfabc. destruct (fab z) eqn:? . inv e. destruct (fc z) eqn:? . inv e0. auto.
  } exists (exist (finMap (B:=adr)) fabc H2).
  hnf. simpl. intros. rewrite Heqfabc. destruct (fab x) eqn:? .
  + destruct (fc x) eqn:? .
    - destruct a as [fa ?]. destruct b as [fb ?]. hnf in *. simpl in *.
      specialize (H x). rewrite Heqo in *. inversion H.
      * specialize (H0 x). rewrite H6, Heqo0 in *. inversion H0. inversion H9.
      * specialize (H1 x). rewrite H6, Heqo0 in *. inversion H1. inversion H9.
      * inversion H6.
    - constructor.
  + destruct (fc x) eqn:? .
    - constructor.
    - constructor.
Defined.

Definition adr_conflict (a1 a2 : adr) : bool := if (eq_nat_dec a1 a2) then true else false.

Instance AbsAddr_world : AbsAddr adr adr.
  apply (mkAbsAddr adr adr adr_conflict); intros; unfold adr_conflict in *.
  + destruct (eq_nat_dec p1 p2). subst. destruct (eq_nat_dec p2 p2); auto. exfalso; tauto.
    destruct (eq_nat_dec p2 p1). subst. exfalso; tauto. trivial.
  + destruct (eq_nat_dec p1 p1). inversion H. exfalso; tauto.
Defined.

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
