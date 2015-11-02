Lemma exists_aux: forall P: Prop, (exists H: P, let H' := H in True) -> P.
Proof.
  intros.
  destruct H; auto.
Qed.

Ltac gather_current_goal_with_evar := apply exists_aux; eexists; exact I.

