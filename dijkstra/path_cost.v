Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.AdjMatGraph.
Require Import RamifyCoq.dijkstra.MathDijkGraph.
Require Import RamifyCoq.dijkstra.SpaceDijkGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Lemma if_true_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = true -> (if b then a else c) = a.
Proof. intros. rewrite H. trivial. Qed.

Lemma if_false_bool:
  forall (T : Type) (a : T) (b : bool) (c : T),
    b = false -> (if b then a else c) = c.
Proof. intros. rewrite H. trivial. Qed.

Definition careful_add a b :=
  if a =? 0 then b else
    if b =? 0 then a else
      if orb (a <? 0) (b <? 0) then -1 else
        if inf <=? (a + b) then inf else a + b.

Lemma careful_add_id:
  forall a, careful_add a 0 = a.
Proof.
  intros. unfold careful_add. simpl.
  destruct (a =? 0) eqn:?; trivial.
  rewrite Z.eqb_eq in Heqb. lia.
Qed.

Lemma careful_add_comm:
  forall a b, careful_add a b = careful_add b a.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0) eqn:?; destruct (b =? 0) eqn:?; trivial.
  1: try rewrite Z.eqb_eq in *; lia.
  destruct (a <? 0) eqn:?; destruct (b <? 0) eqn:?;
           simpl; trivial.
  destruct (inf <=? a + b) eqn:?;
           rewrite Z.add_comm in Heqb4; rewrite Heqb4; lia.
Qed.

Lemma careful_add_assoc:
  forall a b c,
    careful_add a (careful_add b c) =
    careful_add (careful_add a b) c.
Proof.
  intros.
  unfold careful_add.
  destruct (a =? 0) eqn:?;
           destruct (b =? 0) eqn:?;
           destruct (c =? 0) eqn:?;
           try rewrite Heqb0; try rewrite Heqb1;
    try rewrite Heqb2; trivial.
  - destruct (a <? 0) eqn:?;
             destruct (b <? 0) eqn:?;
             destruct (c <? 0) eqn:?; simpl; trivial.
    + destruct (inf <=? a + b) eqn:?.
      1: rewrite if_false_bool; trivial.
      rewrite if_false_bool; trivial.
      rewrite Z.eqb_neq, Z.ltb_nlt in *; lia.
    + destruct (inf <=? a + b) eqn:?.
      1: rewrite if_false_bool; trivial.
      destruct (a + b =? 0) eqn:?; trivial.
      rewrite Z.eqb_eq in *; lia.
  - destruct (a <? 0) eqn:?;
             destruct (b <? 0) eqn:?;
             destruct (c <? 0) eqn:?; simpl; trivial.
    + rewrite if_false_bool; trivial.
      destruct (inf <=? b + c) eqn:?.
      * compute; trivial.
      * rewrite Z.eqb_neq, Z.ltb_nlt in *; lia.
    + destruct (inf <=? a + b) eqn:?.
      * compute; trivial.
      * rewrite if_false_bool.
        2: rewrite Z.eqb_neq, Z.ltb_nlt in *; lia.
        rewrite Bool.orb_true_r; trivial.
    + rewrite Z.eqb_neq, Z.ltb_ge in *.
      rewrite if_false_bool.
      2: { destruct (inf <=? b + c).
           - compute; trivial.
           - rewrite Z.eqb_neq; lia. }
      destruct (inf <=? b + c) eqn:?.
      * rewrite if_false_bool by (compute; trivial).
        rewrite if_true_bool.
        2: rewrite Z.leb_le; lia.
        rewrite if_false_bool.
        2: { destruct (inf <=? a + b) eqn:?.
             - compute; trivial.
             - rewrite Z.eqb_neq; lia. }
        rewrite Bool.orb_false_r.
        rewrite if_false_bool.
        2: { destruct (inf <=? a + b) eqn:?.
             - compute; trivial.
             - rewrite Z.ltb_nlt; lia. }
        destruct (inf <=? a + b) eqn:?.
        -- rewrite if_true_bool; trivial.
           rewrite Z.leb_le; lia. 
        -- rewrite if_true_bool; trivial.
           rewrite Z.leb_le in *; lia. 
      * rewrite if_false_bool by (rewrite Z.ltb_nlt; lia).
        rewrite Z.add_assoc.
        destruct (inf <=? a + b + c) eqn:?.
        -- rewrite if_false_bool.
           2:  { destruct (inf <=? a + b) eqn:?.
                 - compute; trivial.
                 - rewrite Z.eqb_neq; lia. }
           rewrite Bool.orb_false_r.
           rewrite if_false_bool.
           2:  { destruct (inf <=? a + b) eqn:?.
                 - compute; trivial.
                 - rewrite Z.ltb_nlt; lia. }
           rewrite if_true_bool; trivial.
           destruct (inf <=? a + b) eqn:?; trivial.
           rewrite Z.leb_le. lia.
        -- rewrite if_false_bool.
           rewrite if_false_bool.
           rewrite if_false_bool.
           rewrite if_false_bool; trivial.
           all: rewrite Z.leb_gt in *.
           1: lia.
           1: { rewrite if_false_bool; trivial.
                rewrite Z.leb_gt in *; lia. }
           1: { rewrite Bool.orb_false_r.
                rewrite if_false_bool.
                rewrite Z.ltb_nlt; lia.
                rewrite Z.leb_gt; lia. }
           destruct (inf <=? a + b) eqn:?.
           ++ compute; trivial.
           ++ rewrite Z.eqb_neq; lia.
Qed.

Lemma careful_add_clean:
  forall a b,
    0 <= a -> 0 <= b -> a + b < inf ->
    careful_add a b = a + b.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0) eqn:?;
           destruct (b =? 0) eqn:?;
           try rewrite Z.eqb_eq in *;
    try rewrite Z.eqb_neq in *; subst; try lia.
  rewrite if_false_bool.
  rewrite if_false_bool; trivial.
  rewrite Z.leb_gt; trivial.
  rewrite Bool.orb_false_iff.
  split; rewrite Z.ltb_nlt; lia.
Qed.

Lemma careful_add_dirty:
  forall a b,
    a < inf -> b < inf ->
    a + b >= inf ->
    careful_add a b = inf.
Proof.
  intros.
  unfold careful_add.
  destruct (a =? 0) eqn:?;
           destruct (b =? 0) eqn:?;
  try rewrite Z.eqb_eq in *;
    try rewrite Z.eqb_neq in *.
  - subst. exfalso. compute in H1. apply H1; trivial.
  - exfalso. lia.
  - exfalso. lia.
  - destruct (a <? 0) eqn:?; simpl.
    + rewrite Z.ltb_lt in Heqb2. lia.
    + destruct (b <? 0) eqn:?; simpl.
      * rewrite Z.ltb_lt in Heqb3. lia.
      * rewrite if_true_bool; trivial.
        rewrite Z.leb_le. lia.
Qed.

Lemma careful_add_pos:
  forall a b,
    0 <= a -> 0 <= b -> 0 <= careful_add a b.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0); destruct (b =? 0); trivial.
  rewrite if_false_bool.
  2: { rewrite Bool.orb_false_iff; split;
       rewrite Z.ltb_nlt; lia. }
  destruct (inf <=? a + b); [now compute| lia].
Qed.

Lemma careful_add_inf:
  forall a,
    0 <= a -> careful_add a inf = inf.
Proof.
  intros. unfold careful_add.
  destruct (a =? 0); trivial.
  rewrite if_false_bool by (now compute).
  rewrite if_false_bool.
  2: { rewrite Bool.orb_false_iff; split;
       rewrite Z.ltb_nlt; [lia | compute; inversion 1]. }
  rewrite if_true_bool; trivial. rewrite Z.leb_le. lia.
Qed.

Lemma careful_add_inf_clean:
  forall a b,
    0 <= a -> 0 <= b ->
    careful_add a b < inf ->
    a + b < inf.
Proof.
  intros.
  unfold careful_add in H1.
  destruct (a =? 0) eqn:?.
  - rewrite Z.eqb_eq in *. lia.
  - destruct (b =? 0) eqn:?.
    + rewrite Z.eqb_eq in *. lia.
    + rewrite Z.eqb_neq in *.
      destruct (a <? 0) eqn:?; destruct (b <? 0) eqn:?;
               try rewrite Z.ltb_lt in *; try lia.
      simpl in H1.
      destruct (inf <=? a + b); [inversion H1 | trivial].
Qed.

(**** PATH COST w/ CAREFUL_ADD ****)

Definition path_cost (g : DijkstraGeneralGraph) (path : @path V E) : DE :=
  fold_left careful_add (map (elabel g) (snd path)) 0.

Lemma one_step_path_Znth:
  forall g a b,
    sound_dijk_graph g ->
    evalid g (a, b) ->
    path_cost g (a, (a,b)::nil) =
    elabel g (a,b).
Proof.
  intros.
  unfold path_cost; simpl.
  rewrite careful_add_comm, careful_add_id; trivial.
Qed.

Lemma acc_pos: forall (g : DijkstraGeneralGraph) l z,
    (forall e : E, In e l -> 0 <= elabel g e) -> 0 <= z ->
    0 <= fold_left careful_add (map (elabel g) l) z.
Proof.
  intro. induction l; intros; simpl; auto. apply IHl.
  - intros. apply H. now apply in_cons.
  - unfold careful_add.
    destruct (z =? 0).
    1: apply H, in_eq.
    destruct (elabel g a =? 0).
    1: apply H0.
    rewrite if_false_bool.
    2: rewrite Bool.orb_false_iff; split; rewrite Z.ltb_nlt;
      [lia | apply Zle_not_lt, H, in_eq].
    destruct (inf <=? z + elabel g a).
    compute; inversion 1.
    apply Z.add_nonneg_nonneg; auto; apply H, in_eq.
Qed.

Lemma path_cost_pos:
  forall g p,
    sound_dijk_graph g ->
    valid_path g p ->
    inrange_graph g ->
    0 <= path_cost g p.
Proof.
  intros.
  destruct p as [src links]. unfold path_cost. simpl.
  assert (forall e, In e links -> evalid g e). {
    intros. eapply valid_path_evalid; eauto. }
  assert (forall e, In e links -> 0 <= elabel g e). {
    intros. apply inrange_graph_cost_pos; auto. }
  apply acc_pos; auto. easy.
Qed.

Lemma path_cost_app_cons:
  forall g path i,
    sound_dijk_graph g ->
    valid_path g path ->
    inrange_graph g ->
    elabel g i + path_cost g path < inf ->
    evalid g i ->
    path_cost g (fst path, snd path +:: i) =
    path_cost g path + elabel g i.
Proof.
  intros.
  unfold path_cost in *. simpl.
  rewrite map_app, fold_left_app. simpl.
  pose proof (path_cost_pos g path) H H0 H1.
  assert (0 <= elabel g i) by
      (apply inrange_graph_cost_pos; trivial).
  apply careful_add_clean; trivial; lia.
Qed.

Lemma path_cost_init:
  forall l init s,
    init < inf ->
    fold_left careful_add l (careful_add init s) =
    careful_add init (fold_left careful_add l s).
Proof.
  intros.
  generalize dependent s.
  induction l.
  - intros; simpl. unfold careful_add.
    destruct (init =? 0) eqn:?; trivial.
  - intros; simpl.
    rewrite <- careful_add_assoc.
    rewrite IHl. lia.
Qed.

Lemma path_cost_path_glue:
  forall g p1 p2,
    path_cost g p1 < inf ->
    path_cost g (path_glue p1 p2) = careful_add (path_cost g p1) (path_cost g p2).
Proof.
  intros.
  unfold path_cost at 1, path_glue at 1.
  simpl. rewrite map_app.
  rewrite fold_left_app.
  assert ((fold_left careful_add (map (elabel g) (snd p1)) 0) = (path_cost g p1))
    by now unfold path_cost.
  Set Printing All.  
  unfold DE in *.
  rewrite H0. 
  unfold path_cost at 3.
  remember (map (elabel g) (snd p2)) as l2.
  unfold DE in *.
  rewrite <- Heql2.
  Unset Printing All.
  remember (path_cost g p1) as c1.
  replace c1 with (careful_add c1 0) at 1 by
      apply careful_add_id. 
  rewrite path_cost_init; trivial.
Qed.

Lemma path_cost_init_inf:
  forall l init s,
    0 <= s ->
    inf <= init ->
    Forall (fun a => 0 <= a) l ->
    fold_left careful_add l (careful_add init s) >=
    inf.
Proof.
  intros.
  generalize dependent s.
  induction l.
  - intros; simpl. unfold careful_add.
    destruct (init =? 0) eqn:?; trivial.
    + rewrite Z.eqb_eq in Heqb. rewrite Heqb in H0.
      compute in H0. exfalso; apply H0; trivial.
    + destruct (s =? 0); [lia|].
      rewrite if_false_bool.
      rewrite if_true_bool. lia.
      rewrite Z.leb_le. lia.
      rewrite Bool.orb_false_iff; split;
        rewrite Z.ltb_ge; try lia.
      assert (0 < inf) by now compute.
      lia.
  - intros. simpl.
    rewrite <- careful_add_assoc.
    apply IHl.
    + apply Forall_tl with (x := a); trivial.
    + rewrite Forall_forall in H1.
      apply careful_add_pos; trivial.
      apply H1. apply in_eq.
Qed.

Lemma path_cost_path_glue_ge_inf:
  forall g p1 p2,
    sound_dijk_graph g ->
    valid_path g p1 ->
    valid_path g p2 ->
    inrange_graph g ->
    inf <= path_cost g p1 ->
    path_cost g (path_glue p1 p2) >= inf.
Proof.
  intros.
  unfold path_cost, path_glue. simpl.
  rewrite map_app.
  rewrite fold_left_app.
  assert ((fold_left careful_add (map (elabel g) (snd p1)) 0) = (path_cost g p1))
    by now unfold path_cost.
  Set Printing All.
  unfold DE in *. rewrite H4. 
  Unset Printing All.
  rewrite <- (careful_add_id (path_cost g p1)).
  apply path_cost_init_inf; trivial.
  lia.
  rewrite Forall_forall. intros.
  rewrite in_map_iff in H5. destruct H5 as [? [? ?]].
  rewrite <- H5.
  apply inrange_graph_cost_pos; trivial.
  rewrite (surjective_pairing p2) in *. simpl in H6.
  apply (valid_path_evalid g _ _ _ H1 H6).
Qed.

Lemma path_cost_path_glue_lt:
  forall g p1 p2,
    sound_dijk_graph g ->
    valid_path g p1 ->
    valid_path g p2 ->
    inrange_graph g ->
    path_cost g (path_glue p1 p2) < inf ->
    path_cost g p1 < inf /\ path_cost g p2 < inf.
Proof.
  intros.
  destruct (path_cost g p1 <? inf) eqn:?.
  - rewrite Z.ltb_lt in Heqb.
    split; trivial.
    rewrite path_cost_path_glue in H3; trivial.
    destruct (path_cost g p2 <? inf) eqn:?.
    1: rewrite Z.ltb_lt in Heqb0; trivial.
    exfalso. unfold careful_add in H3.
    destruct (path_cost g p1 =? 0).
    1: rewrite Z.ltb_nlt in Heqb0; lia.
    destruct (path_cost g p2 =? 0) eqn:?.
    + rewrite Z.ltb_nlt in Heqb0.
      rewrite Z.eqb_eq in Heqb1.
      apply Heqb0. rewrite Heqb1. compute. trivial.
    + rewrite if_false_bool in H3.
      rewrite if_true_bool in H3.
      * lia.
      * rewrite Z.leb_le.
        rewrite Z.ltb_ge in Heqb0.
        assert (0 <= path_cost g p1) by (apply path_cost_pos; trivial). 
        lia.
      * rewrite Bool.orb_false_iff; split; rewrite Z.ltb_ge;
          apply path_cost_pos; trivial.
  - rewrite Z.ltb_ge in Heqb.
    exfalso.
    pose proof (path_cost_path_glue_ge_inf _ _ _ H H0 H1 H2 Heqb).
    lia.
Qed.

Lemma in_path_app_cons:
  forall g step p2a src a b,
    sound_dijk_graph g ->
    path_ends g p2a src a ->
    In_path g step (fst p2a, snd p2a +:: (a, b)) ->
    In_path g step p2a \/ step = b.
Proof.
  intros. destruct H1; simpl in H1.
  - left. unfold In_path. left; trivial.
  - destruct H1 as [? [? ?]].
    apply in_app_or in H1.
    destruct H as [? [? [? ?]]].
    unfold src_edge in H4. unfold dst_edge in H5.
    rewrite H4, H5 in H2.
    destruct H1.
    + left. unfold In_path. right.
      exists x. rewrite H4, H5. split; trivial.
    + simpl in H1. destruct H1; [|lia].
      rewrite (surjective_pairing x) in *.
      inversion H1. simpl in H2.
      destruct H2.
      * left. destruct H0.
        apply pfoot_in in H6. rewrite H7, <- H2 in H6.
        trivial.
      * right; trivial.
Qed.
