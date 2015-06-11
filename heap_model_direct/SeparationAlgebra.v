Require Import VST.msl.msl_direct.
Require Import FunctionalExtensionality.
Require Import RamifyCoq.msl_ext.ramify_tactics.

Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
Proof. constructor; intros; inv H. Qed.

Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
Proof. repeat intro. inv H. Qed.

Definition var := nat.
Definition adr := nat.

Definition world := (fpm adr adr).

Instance Join_world: Join world := Join_fpm (Join_discrete adr).

Instance Perm_world : Perm_alg world. apply Perm_fpm; apply Perm_discrete. Qed.

Instance Sep_world : Sep_alg world. apply Sep_fpm. Qed.

Instance Canc_world : Canc_alg world. apply Canc_fpm; [intuition | repeat intro; inversion H]. Qed.

Instance Disj_world : Disj_alg world. apply Disj_fpm; repeat intro; inversion H. Qed.

Instance Cross_world : Cross_alg world. apply Cross_fpm; [apply Perm_discrete | apply psa_discrete | repeat intro; inv H]. Qed.

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
