Require Import VST.floyd.proofauto.
Require Import CertiGraph.graph.MathAdjMatGraph.

Definition eformat (e: E) := if fst e <=? snd e then e else (snd e, fst e).

Lemma eformat1: forall (e: E), fst e <= snd e -> eformat e = e.
Proof. unfold eformat; intros. rewrite Zle_is_le_bool in H; rewrite H. auto. Qed.

Lemma eformat2': forall (e: E), snd e < fst e -> eformat e = (snd e, fst e).
Proof. unfold eformat; intros. rewrite <- Z.leb_gt in H; rewrite H. auto. Qed.

Lemma eformat2: forall (e: E), snd e <= fst e -> eformat e = (snd e, fst e).
Proof.
  intros. apply Z.le_lteq in H. destruct H. rewrite eformat2'; auto. rewrite eformat1, H. rewrite <- H at 2. destruct e; auto. lia.
Qed.

Lemma eformat_eq:
  forall u v a b, eformat (u,v) = eformat (a,b) -> ((u=a /\ v=b) \/ (u=b /\ v=a)).
Proof.
  intros. destruct (Z.le_ge_cases u v); destruct (Z.le_ge_cases a b).
  rewrite eformat1, eformat1 in H. apply pair_equal_spec in H. left; auto. simpl; auto. simpl; auto. simpl; auto.
  rewrite eformat1, eformat2 in H. simpl in H. apply pair_equal_spec in H. right; auto. simpl; auto. simpl; auto.
  rewrite eformat2, eformat1 in H. simpl in H. apply pair_equal_spec in H. right; split; apply H. simpl; auto. simpl; auto.
  rewrite eformat2, eformat2 in H. simpl in H. apply pair_equal_spec in H. left; split; apply H. simpl; auto. simpl; auto.
Qed.

Lemma eformat_symm:
  forall u v, eformat (u,v) = eformat (v,u).
Proof.
  intros. destruct (Z.lt_trichotomy u v).
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  destruct H.
  rewrite eformat1. rewrite eformat2. simpl; auto. simpl; lia. simpl; lia.
  rewrite eformat2'. rewrite eformat1. simpl; auto. simpl; lia. simpl; lia.
Qed.
