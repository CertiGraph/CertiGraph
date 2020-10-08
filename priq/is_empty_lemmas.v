Require Import VST.floyd.proofauto.

Section IsEmptyLemmas.

  Context {inf: Z}.

  (* isEmpty and lemmas about it *)

  Definition isEmpty (priq : list Z) : val :=
    fold_right
      (fun h acc =>
         if (Z_lt_dec h (inf + 1)) then Vzero else acc)
      Vone priq.

  Lemma isEmpty_in: forall l target,
      In target l ->
      target < inf + 1 ->
      isEmpty l = Vzero.
  Proof.
    intros. induction l.
    1: exfalso; apply (in_nil H).
    unfold isEmpty. rewrite fold_right_cons.
    destruct (Z_lt_dec a (inf+1)); trivial.
    simpl in H; simpl; destruct H.
    1: rewrite H in n; exfalso; lia.
    clear n a. specialize (IHl H).
    unfold isEmpty in IHl. trivial.
  Qed.

  Lemma isEmpty_in': forall l,
      (exists i, In i l /\ i < (inf + 1)) <->
      isEmpty l = Vzero.
  Proof.
    split; intros.
    - destruct H as [? [? ?]]. induction l.
      1: exfalso; apply (in_nil H).
      unfold isEmpty. rewrite fold_right_cons.
      destruct (Z_lt_dec a (inf+1)); trivial.
      simpl in H; simpl; destruct H.
      1: rewrite H in n; exfalso; lia.
      clear n a. specialize (IHl H).
      unfold isEmpty in IHl. trivial.
    - induction l.
      1: inversion H.
      simpl in H. destruct (Z_lt_dec a (inf+1)).
      + exists a. split; simpl; [left|]; trivial.
      + destruct (IHl H) as [? [? ?]].
        exists x. split; [apply in_cons|]; assumption.
  Qed.

  Lemma isEmptyTwoCases: forall l,
      isEmpty l = Vone \/ isEmpty l = Vzero.
  Proof.
    intros. induction l. 1: simpl; left; trivial.
    destruct IHl; simpl; destruct (Z_lt_dec a (inf+1));
      (try now left); now right.
  Qed.

  Lemma isEmptyMeansInf: forall l,
      isEmpty l = Vone <->
      Forall (fun x => x > inf) l.
  Proof.
    intros.
    split; intros.
    - induction l; trivial. simpl in H.
      destruct (Z_lt_dec a (inf+1)); [inversion H|].
      specialize (IHl H). apply Forall_cons; trivial. lia.
    - induction l; trivial. simpl.
      destruct (Z_lt_dec a (inf+1)).
      2: { apply IHl.
           rewrite Forall_forall; intros.
           rewrite Forall_forall in H. simpl in H.
           apply H. right; trivial.
      }
      exfalso.
      rewrite Forall_forall in H.
      assert (In a (a :: l)) by (apply in_eq).
      specialize (H _ H0). lia.
  Qed.

  Lemma isEmpty_Vone_app: forall l1 l2,
      isEmpty (l1 ++ l2) = Vone <->
      isEmpty l1 = Vone /\ isEmpty l2 = Vone.
  Proof.
    intros. split; intros.
    - repeat rewrite isEmptyMeansInf, Forall_forall in *;
        split; intros; apply H, in_or_app;
          [left | right]; trivial.
    - repeat rewrite isEmptyMeansInf, Forall_forall in *.
      destruct H. intros.
      apply in_app_or in H1; destruct H1;
        [apply H | apply H0]; trivial.
  Qed.

End IsEmptyLemmas.
