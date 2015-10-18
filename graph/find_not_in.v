Require Import Coq.Classes.EquivDec.
Require Import RamifyCoq.lib.List_ext.

Section FIND_NOT_IN.
Context {V: Type}.
Context {EDV: EqDec V eq}.
 
Fixpoint findNotIn (l1 l2 l3: list V) : (option V * (list V * list V)) :=
  match l1 with
    | nil => (None, (nil, nil))
    | x :: l => if (in_dec equiv_dec x l2) then findNotIn l l2 (x :: l3) else (Some x, (rev l3, l))
  end.
 
Lemma find_not_in_none: forall l1 l2 l3, fst (findNotIn l1 l2 l3) = None -> Forall (fun m => In m l2) l1.
Proof.
  induction l1; intros. apply Forall_nil. simpl in H. destruct (in_dec equiv_dec a l2).
  apply Forall_cons. auto. apply IHl1 with (a :: l3); auto. inversion H.
Qed.
 
Lemma find_not_in_some_explicit:
  forall l1 l2 l3 x li1 li2,
    findNotIn l1 l2 l3 = (Some x, (li1, li2)) -> (Forall (fun m => In m l2) l3) ->
    (~ In x li1) /\ (~ In x l2) /\ exists l4, li1 = rev l3 ++ l4 /\ Forall (fun m => In m l2) l4 /\ l1 = l4 ++ x :: li2.
Proof.
  induction l1; intros; simpl in H. inversion H. destruct (in_dec equiv_dec a l2).
  assert (Forall (fun m : V => In m l2) (a :: l3)) by (apply Forall_cons; auto).
  specialize (IHl1 l2 (a :: l3) x li1 li2 H H1). destruct IHl1 as [? [? [l4 [? [? ?]]]]]. split; auto. split; auto.
  exists (a :: l4). repeat split; auto. simpl in H4. rewrite <- app_assoc in H4. rewrite <- app_comm_cons in H4.
  rewrite app_nil_l in H4. auto. rewrite H6; apply app_comm_cons. inversion H. split. intro; apply n.
  rewrite Forall_forall in H0. apply (H0 a). rewrite H2. rewrite in_rev. auto. split. rewrite <- H2. auto.
  exists nil. repeat split; auto. rewrite app_nil_r. auto.
Qed.
 
Lemma find_not_in_some:
  forall l1 l2 x li1 li2,
    findNotIn l1 l2 nil = (Some x, (li1, li2)) ->
    Forall (fun m => In m l2) li1 /\ l1 = li1 ++ x :: li2 /\ ~ In x li1 /\ ~ In x l2.
Proof.
  intros. assert (Forall (fun m : V => In m l2) nil) by apply Forall_nil.
  destruct (find_not_in_some_explicit l1 l2 nil x li1 li2 H H0). destruct H2 as [? [l4 [? [? ?]]]].
  simpl in H3. rewrite H3 in *. repeat split; auto.
Qed.
 
End FIND_NOT_IN.

