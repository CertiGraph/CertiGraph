Lemma exists_aux: forall P: Prop, (exists H: P, H = H) -> P.
Proof.
  intros.
  destruct H; auto.
Qed.

Ltac gather_current_goal_with_evar := apply exists_aux; eexists; reflexivity.