Require Export VST.floyd.proofauto.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import Coq.Lists.List.
Require Export RamifyCoq.sample_mark.dijk_pq_arr_macros.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).


(*
 Concretizing the DijkstraGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  | list DE |  Z  | unit |  Finite   | 
 *)

Definition VType : Type := Z.
Definition EType : Type := VType * VType.
Definition ElabelType : Type := Z. (* labels are in Z *)
Definition LE : Type := ElabelType.
Definition LV: Type := list LE.
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec v v0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Lemma nat_inc_list_Zlength:
  forall n, Zlength (nat_inc_list n) = Z.of_nat n.
Proof.
  intros. now rewrite Zlength_correct, nat_inc_list_length. Qed.

Lemma nat_inc_list_i: forall i n,
    0 <= i < Z.of_nat n ->
    Znth i (nat_inc_list n) = i.
Proof.
  intros. generalize dependent i. induction n.
  1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; lia.
  intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
  apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
  - rewrite app_Znth1. apply IHn. lia.
    now rewrite nat_inc_list_Zlength.
  - rewrite app_Znth2 by (rewrite nat_inc_list_Zlength; lia). 
    rewrite H0. rewrite nat_inc_list_Zlength. simpl. 
    replace (Z.of_nat n - Z.of_nat n) with 0 by lia.
    rewrite Znth_0_cons; trivial.
Qed.

Definition DijkstraLabeledGraph := LabeledGraph VType EType LV LE LG.

Class Fin (g: DijkstraLabeledGraph) :=
  { fin: FiniteGraph g; }.

Definition DijkstraGeneralGraph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

Definition vertex_valid (g : DijkstraGeneralGraph): Prop :=
  forall v, vvalid g v <-> 0 <= v < SIZE.

Definition edge_valid (g : DijkstraGeneralGraph): Prop :=
  forall a b, evalid g (a,b) <->
            (vvalid g a /\ vvalid g b).

Definition src_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, src g e = fst e.

Definition dst_edge (g : DijkstraGeneralGraph): Prop :=
  forall e, dst g e = snd e.

Definition sound_dijk_graph (g : DijkstraGeneralGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ src_edge g /\ dst_edge g.

(* Moving on to Spatial Rep *)

Section SpaceDijkstraArrayGraph.
  
  Class SpatialDijkstraArrayGraphAssum (Pred : Type):=
    {
    SGP_ND: NatDed Pred;
    SGP_SL : SepLog Pred;
    SGP_ClSL: ClassicalSep Pred;
    SGP_CoSL: CorableSepLog Pred
    }.
  
  Class SpatialDijkstraArrayGraph (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list Z -> Pred.

  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAGP: SpatialDijkstraArrayGraphAssum Pred}.
  Context {SAG: SpatialDijkstraArrayGraph Addr Pred}.

  Definition vert_rep (g : DijkstraGeneralGraph) (v : VType) : list Z :=
    map (elabel g) (map (fun x => (v,x)) (nat_inc_list (Z.to_nat SIZE))).
  
  (* from Graph to list (list Z) *)
  Definition graph_to_mat (g : DijkstraGeneralGraph) : list (list Z) :=
    map (vert_rep g) (nat_inc_list (Z.to_nat SIZE)).
  
  (* spatial representation of the DijkstraGraph *)
  Definition graph_rep (g : DijkstraGeneralGraph) (a : Addr)  :=
    abstract_data_at a (concat (graph_to_mat g)).

End SpaceDijkstraArrayGraph.

Lemma graph_to_mat_Zlength: forall g, Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; auto. now vm_compute.
Qed.

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

Definition path_cost (g : DijkstraGeneralGraph) (path : @path VType EType) : ElabelType :=
  fold_left careful_add (map (elabel g) (snd path)) 0.

Definition inrange_graph grph_contents :=
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE \/
    Znth i (Znth j grph_contents) = inf.

Lemma elabel_Znth_graph_to_mat:
  forall g src dst,
    sound_dijk_graph g ->
    evalid (pg_lg g) (src, dst) ->
    elabel g (src, dst) =
    Znth dst (Znth src (graph_to_mat g)).
Proof.
  intros. 
  unfold graph_to_mat.
  destruct H as [? [? _]].
  red in H, H1.
  rewrite H1 in H0; destruct H0. 
  rewrite H in H0, H2.
  rewrite Znth_map, nat_inc_list_i.
  unfold vert_rep. rewrite Znth_map.
  rewrite Znth_map. rewrite nat_inc_list_i.
  reflexivity.
  3: rewrite Zlength_map.
  2, 3, 5: rewrite nat_inc_list_Zlength.
  all: rewrite Z2Nat.id; lia.
Qed.

Lemma one_step_path_Znth:
  forall g a b,
    sound_dijk_graph g ->
    evalid g (a, b) ->
    path_cost g (a, (a,b)::nil) =
    Znth b (Znth a (graph_to_mat g)).
Proof.
  intros.
  unfold path_cost; simpl.
  rewrite careful_add_comm, careful_add_id.
  rewrite elabel_Znth_graph_to_mat; trivial.
Qed.

Lemma vvalid2_evalid:
  forall g a b,
    sound_dijk_graph g ->
    vvalid g a ->
    vvalid g b ->
    evalid g (a,b).
Proof.
  intros. destruct H as [_ [? _]].
  red in H; rewrite H; split; trivial.
Qed.

Lemma vvalid_range:
  forall g a,
    sound_dijk_graph g ->
    vvalid g a <-> 0 <= a < SIZE.
Proof.
  intros. destruct H as [? _]. red in H. trivial.
Qed.

Lemma valid_path_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    evalid g (u,i) ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  assert (Hrem := H).
  destruct H as [? [? [? ?]]].
  simpl; split.
  1: rewrite H4; simpl; assumption.
  unfold strong_evalid.
  rewrite H4, H5; simpl.
  split; trivial.
  red in H3; rewrite H3 in H2; trivial.
Qed.

Lemma path_ends_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.
  split.
  + destruct H0; apply H0.
  + rewrite pfoot_last.
    destruct H as [_ [_ [_ ?]]].
    rewrite H; reflexivity.
Qed.

Lemma inrange_graph_cost_pos: forall g e,
    sound_dijk_graph g -> inrange_graph (graph_to_mat g) ->
    evalid g e -> 0 <= elabel g e.
Proof.
  intros. rewrite (surjective_pairing e) in *.
  rewrite elabel_Znth_graph_to_mat; auto. destruct H as [? [? _]].
  red in H, H2.
  rewrite (surjective_pairing e) in H1.
  rewrite H2 in H1. red in H0.
  rewrite (graph_to_mat_Zlength g) in H0.
  simpl in H1. destruct H1. rewrite H in H1, H3.
  specialize (H0 _ _ H3 H1). destruct H0.
  1: destruct H0; lia.
  rewrite H0. compute; inversion 1.
Qed.

Lemma acc_pos: forall (g : DijkstraGeneralGraph) l z,
    (forall e : EType, In e l -> 0 <= elabel g e) -> 0 <= z ->
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
    inrange_graph (graph_to_mat g) ->
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
    inrange_graph (graph_to_mat g) ->
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
  unfold LE, ElabelType in *.
  rewrite H0. 
  unfold path_cost at 3.
  remember (map (elabel g) (snd p2)) as l2.
  unfold LE, ElabelType in *.
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
    inrange_graph (graph_to_mat g) ->
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
  unfold LE, ElabelType in *. rewrite H4. 
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
    inrange_graph (graph_to_mat g) ->
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

Lemma step_in_range: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [? _]]].
  unfold vertex_valid in H.
  unfold src_edge in H2.
  assert (In_path g (fst x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| left]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
Qed.

Lemma step_in_range2: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [_ ?]]].
  unfold vertex_valid in H.
  unfold dst_edge in H2.
  assert (In_path g (snd x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| right]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. lia.
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
