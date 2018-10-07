Require Import VST.floyd.base.
Require Import RamifyCoq.msl_ext.weak_valid_pointer.

Lemma memory_block_weak_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i <= n -> 0 < n -> sepalg.nonidentity sh ->
  memory_block sh n p |-- weak_valid_pointer (offset_val i p).
Proof. exact @memory_block_weak_valid_pointer. Qed.

Local Open Scope logic.

Lemma extend_weak_valid_pointer:
  forall p Q, weak_valid_pointer p * Q |-- weak_valid_pointer p.
Proof.
  intros. unfold weak_valid_pointer.
  pose proof (extend_tc.extend_valid_pointer' p 0).
  pose proof (predicates_hered.boxy_e _ _ H). 
  pose proof (extend_tc.extend_valid_pointer' p (-1)).
  pose proof (predicates_hered.boxy_e _ _ H1).
  change (_ |-- _) with
      (predicates_hered.derives
         (predicates_hered.orp (valid_pointer' p 0) (valid_pointer' p (-1)) * Q)
         (predicates_hered.orp (valid_pointer' p 0) (valid_pointer' p (-1)))).
  intros ? (w1 & w2 & Hj & Hp & ?). simpl in Hp |- * .
  destruct Hp; [left; apply (H0 w1) | right; apply (H2 w1)]; auto; hnf; eauto.
Qed.
