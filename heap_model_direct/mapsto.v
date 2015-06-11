Require Import VST.msl.msl_direct.
Require Import FunctionalExtensionality.
Require Import RamifyCoq.msl_ext.ramify_tactics.
Require Import RamifyCoq.heap_model_direct.SeparationAlgebra.

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

Lemma mapsto_unique: forall x a b w, ~ (mapsto x a * mapsto x b)%pred w.
Proof.
  repeat intro. destruct_sepcon H h. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]]. destruct h1 as [f1 m1].
  destruct h2 as [f2 m2]. destruct w as [fw mw]. hnf in *. simpl in *. specialize (H x). rewrite H3 in *. rewrite H5 in *.
  inversion H. inversion H9.
Qed.
