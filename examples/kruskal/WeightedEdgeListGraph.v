Require Import VST.floyd.proofauto.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.FiniteGraph.
Require Export CertiGraph.graph.undirected_graph.

Section EdgeListModel.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(* Concretizing the EdgelistGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  |   unit  |  Z  | unit |  Finite   |
*)

Definition VType : Type := Z. (*0...V-1*)
Definition EType : Type := VType * VType.
Definition LE : Type := Z. (*weight*)
Definition LV: Type := unit. (*I don't think we need this*)
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

Context {size : Z}.
Context {sizebound: 0 <= size <= Int.max_signed}.

Definition EdgeListLG := LabeledGraph VType EType LV LE LG.

Class SoundEdgeList (g: EdgeListLG) := {
    sb: 0 <= size <= Int.max_signed;
    vv: forall v, vvalid g v <-> 0 <= v < size;
    ev: forall e, evalid g e -> (vvalid g (src g e) /\ vvalid g (dst g e));
    wv: forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed;
    sf: forall e, evalid g e -> src g e = fst e;
    ds: forall e, evalid g e -> dst g e = snd e;
    fin: FiniteGraph g;
  }.

Definition EdgeListGG := (GeneralGraph VType EType LV LE LG (fun g => SoundEdgeList g)).

Definition EdgeListGG_EdgeListLG
           (g: EdgeListGG) : EdgeListLG := lg_gg g.
Local Coercion EdgeListGG_EdgeListLG: EdgeListGG >-> EdgeListLG.
Local Identity Coercion EdgeListLG_LabeledGraph: EdgeListLG >-> LabeledGraph.

Definition vertex_valid (g: EdgeListGG) :=
  @vv g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition edge_valid (g: EdgeListGG) :=
  @ev g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition weight_valid (g: EdgeListGG) :=
  @wv g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition src_fst (g : EdgeListGG) :=
  @sf g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition dst_snd (g: EdgeListGG) :=
  @ds g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition size_bound (g: EdgeListGG) :=
  @sb g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Definition finite (g: EdgeListGG) :=
  @fin g ((@sound_gg _ _ _ _ _ _ _ _ g)).

Corollary size_representable:
  Int.min_signed <= size <= Int.max_signed.
Proof.
pose proof Int.min_signed_neg. lia.
Qed.

Corollary vertex_bound:
  forall (g: EdgeListGG) v, vvalid g v -> 0 <= v < Int.max_signed.
Proof.
intros. apply (vertex_valid g) in H. lia.
Qed.

Corollary vertex_representable:
  forall (g: EdgeListGG) v, vvalid g v -> Int.min_signed <= v < Int.max_signed.
Proof.
intros. apply (vertex_valid g) in H.
pose proof Int.min_signed_neg. lia.
Qed.

Instance finGraph (g: EdgeListGG): FiniteGraph g := @fin g (@sound_gg _ _ _ _ _ _ _ _ g).

Lemma evalid_strong_evalid:
  forall (g: EdgeListGG) e, evalid g e -> strong_evalid g e.
Proof.
intros. split. auto. apply edge_valid. apply H.
Qed.

Lemma evalid_uv_vvalid:
  forall (g: EdgeListGG) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply evalid_strong_evalid in H. destruct H. destruct H0.
rewrite src_fst in H0 by auto. rewrite dst_snd in H1 by auto.
split. apply H0. apply H1.
Qed.

Definition numV (g: EdgeListGG) : Z := Zlength (VList g).
Definition numE (g: EdgeListGG) : Z := Zlength (EList g).
(*
Lemma numV_size:
  forall (g: EdgeListGG), numV g = size.
Proof.
intros. unfold numV.
*)
Lemma numE_pos: forall g, 0 <= numE g.
Proof. intros. unfold numE. apply Zlength_nonneg. Qed.

Definition edge_to_wedge (g: EdgeListLG) e : LE * EType := (elabel g e, e).

Definition graph_to_wedgelist (g: EdgeListGG) : list (LE * EType) :=
  map (edge_to_wedge g) (EList g).

Lemma g2wedgelist_numE:
  forall g, Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist. rewrite Zlength_map. trivial.
Qed.

Lemma NoDup_g2wedgelist:
  forall g, NoDup (graph_to_wedgelist g).
Proof.
intros. apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective; intros. inversion H. auto. apply NoDup_EList.
Qed.

Lemma g2wedgelist_evalid:
  forall g w, In w (graph_to_wedgelist g) -> evalid g (snd w).
Proof.
intros. apply list_in_map_inv in H. destruct H; destruct H.
apply EList_evalid in H0. unfold edge_to_wedge in H. inversion H. simpl. auto.
Qed.

Lemma g2wedgelist_repable:
  forall g w, In w (graph_to_wedgelist g) ->
    Int.min_signed <= fst w <= Int.max_signed /\
    Int.min_signed <= fst (snd w) <= Int.max_signed /\
    Int.min_signed <= snd (snd w) <= Int.max_signed.
Proof.
intros. unfold graph_to_wedgelist in H. apply list_in_map_inv in H.
unfold edge_to_wedge in H. destruct H; destruct H. apply EList_evalid in H0.
subst w; simpl. split. apply weight_valid; auto.
rewrite <- (src_fst g), <- (dst_snd g) by auto.
apply evalid_strong_evalid in H0. destruct H0. destruct H0.
rewrite vertex_valid in H0, H1.
set (i:=Int.min_signed); compute in i; subst i.
split; lia.
Qed.

(*****************************PARTIAL LGRAPH AND MSF**********************)
(*These should be abstracted, but we can deal with it after the kruskal proof is done*)

Lemma sound_fits_upath_transfer:
forall p l (g1 g2: EdgeListGG),
(forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) ->
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
intros. apply (fits_upath_transfer'' p l g1 g2); intros.
apply (valid_upath_vvalid g1 p) in H2. apply H; auto.
apply valid_upath_exists_list_edges'. exists l; auto. apply H0; auto.
repeat rewrite src_fst; auto. apply (fits_upath_evalid g1 p l); auto.
repeat rewrite dst_snd; auto. apply (fits_upath_evalid g1 p l); auto.
auto.
Qed.

(***********MSF for edge lists***********)

Definition sum_LE (g: EdgeListGG) : LE :=
  fold_left Z.add (DEList g) 0.

Definition minimum_spanning_forest (t g: EdgeListGG) :=
 labeled_spanning_uforest t g /\
  forall (t': EdgeListGG), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv:
  forall (g: EdgeListGG) (l: list EType),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

(******Back to forests*****)

Lemma forest_bridge1:
  forall (g: EdgeListGG) u v, uforest' g ->
    evalid g (u,v) -> bridge g (u,v) u v.
Proof.
unfold bridge; intros.
apply (forest_edge' p l g). auto. apply evalid_strong_evalid; auto.
rewrite src_fst; auto. rewrite dst_snd; auto. auto.
Qed.

(**********Edgeless graph with V vertices*************)
(*Built off empty WEdgelessGraph*)
(*Skipping an arbitrary list of vertices, because we need NoDup, and our design forbids the skipping of vertices anyway *)

Definition Zseq (z: Z) : list Z := map Z.of_nat (seq 0%nat (Z.to_nat z)).

Lemma Zseq_NoDup:
  forall z, NoDup (Zseq z).
Proof.
unfold Zseq; intros. destruct z; simpl; try apply NoDup_nil.
apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective. apply Nat2Z.inj.
apply seq_NoDup.
Qed.

Lemma Zseq_In:
  forall z x, In x (Zseq z) <-> 0 <= x < z.
Proof.
intros; unfold Zseq; simpl; split; intros.
+ destruct x; destruct z; try inversion H. lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H. rewrite in_seq in H0. lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H.
  assert (Z.neg p < 0) by (apply Pos2Z.neg_is_neg). assert (0 <= Z.of_nat x) by (apply Nat2Z.is_nonneg). lia.
+ destruct x; destruct z; try lia.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p))) 0%nat). rewrite in_seq.
  simpl. lia. rewrite <- positive_nat_Z.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p0))) (Pos.to_nat p)). rewrite in_seq. lia.
Qed.

Corollary Zseq_Zlength:
  forall z, 0 <= z -> Zlength (Zseq z) = z.
Proof.
intros. unfold Zseq. rewrite (Zlength_map nat Z Z.of_nat (seq 0 (Z.to_nat z))).
rewrite Zlength_correct. rewrite seq_length.
apply Z2Nat.id. lia.
Qed.

Section Edgeless_Graph.

Definition edgeless_LG: EdgeListLG :=
@Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG
  (@Build_PreGraph VType EType V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
  (fun v => tt) (fun e => 0) tt.

Instance Sound_edgeless_LG:
  SoundEdgeList edgeless_LG.
Proof.
constructor.
+auto.
+intros; simpl; split; auto.
+intros. simpl in H. contradiction.
+intros. simpl in H. contradiction.
+intros. simpl in H. contradiction.
+intros. simpl in H. contradiction.
+constructor; unfold EnumEnsembles.Enumerable.
exists (Zseq size); split. apply Zseq_NoDup.
unfold edgeless_LG. simpl. intros. apply Zseq_In.
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_GG: EdgeListGG :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG SoundEdgeList
    (EdgeListLG_LabeledGraph edgeless_LG) Sound_edgeless_LG.

Lemma edgeless_GG_vvalid:
  forall k, 0 <= k < size <-> vvalid edgeless_GG k.
Proof.
simpl. intros; split; intros; auto.
Qed.

Lemma edgeless_GG_Permutation:
  Permutation (VList edgeless_GG) (Zseq size).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply Zseq_NoDup.
intros; rewrite Zseq_In. unfold VList; destruct finiteV; simpl.
destruct a. rewrite H0. rewrite edgeless_GG_vvalid. split; auto.
Qed.

Lemma edgeless_GG_numV:
  forall v, 0 <= v -> numV edgeless_GG = size.
Proof.
unfold numV. intros.
assert (Zlength (VList edgeless_GG) = Zlength (Zseq size)).
apply Permutation_Zlength. apply edgeless_GG_Permutation.
rewrite H0. rewrite Zseq_Zlength. auto. lia.
Qed.

Lemma edgeless_GG_evalid:
  forall e, ~ evalid edgeless_GG e.
Proof.
intros. unfold edgeless_GG; simpl. auto.
Qed.

Lemma edgeless_GG_EList:
  EList edgeless_GG = nil.
Proof.
  unfold edgeless_GG, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Corollary edgeless_GG_numE:
  numE edgeless_GG = 0.
Proof.
unfold numE. rewrite edgeless_GG_EList. apply Zlength_nil.
Qed.

Corollary graph_to_wedgelist_edgeless_GG:
  graph_to_wedgelist edgeless_GG = nil.
Proof.
unfold graph_to_wedgelist; intros. rewrite edgeless_GG_EList. auto.
Qed.

Lemma uforest'_edgeless_GG:
  uforest' edgeless_GG.
Proof.
split; intros.
(*no self-loops*)
apply edgeless_GG_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_GG_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_GG_evalid in H; contradiction.
(*main forest definition*)
unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

End Edgeless_Graph.

(***********ADDING A SINGLE EDGE************)

Section EdgeListGG_add.

Context {g: EdgeListGG}.
Context {u v: VType} {w: LE}.
Context {ubound: 0 <= u < size}.
Context {vbound: 0 <= v < size}.
Context {wbound: Int.min_signed <= w <= Int.max_signed}.

(**Adding is necessary for the kruskal algorithm**)
Definition EdgeListLG_adde :=
  labeledgraph_add_edge g (u,v) u v w.

Instance Sound_EdgeListLG_adde:
  SoundEdgeList EdgeListLG_adde.
Proof.
constructor.
+auto.
+intros; simpl; rewrite vertex_valid. split; auto.
+intros. simpl in H. unfold addValidFunc in H. simpl. unfold updateEdgeFunc. unfold equiv_dec.
destruct H. destruct (E_EqDec (u,v) e). hnf in e0. subst e.
pose proof (edge_valid g (u,v) H). rewrite src_fst, dst_snd in H0 by auto. apply H0. apply edge_valid; auto.
subst e. destruct (E_EqDec (u,v) (u,v)). repeat rewrite vertex_valid. split; auto.
unfold complement, equiv in c. contradiction.
+simpl; unfold addValidFunc, update_elabel, equiv_dec; intros.
destruct H. destruct (E_EqDec (u,v) e). auto. apply weight_valid; auto.
subst e. destruct (E_EqDec (u,v) (u,v)). auto. unfold complement, equiv in c; contradiction.
+simpl; unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
destruct H. destruct E_EqDec. unfold equiv in e0. subst e. auto. apply src_fst; auto.
subst e. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
+simpl; unfold addValidFunc, updateEdgeFunc, equiv_dec; intros.
destruct H. destruct E_EqDec. unfold equiv in e0. subst e. auto. apply dst_snd; auto.
subst e. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
+constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc. destruct (in_dec E_EqDec (u,v) (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists ((u,v)::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Definition EdgeListGG_adde: EdgeListGG :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG SoundEdgeList
    (EdgeListLG_LabeledGraph EdgeListLG_adde)
    Sound_EdgeListLG_adde.

Corollary adde_numV:
  numV EdgeListGG_adde = numV g.
Proof.
intros. unfold EdgeListGG_adde. unfold numV. simpl. unfold VList.
destruct finiteV. destruct finiteV. simpl. simpl in a.
destruct a. destruct a0. assert (Permutation x x0). apply NoDup_Permutation; auto.
intros. rewrite H0. rewrite H2. split; auto.
apply Permutation_Zlength. auto.
Qed.

(*should add an EList1 where e is already in g, but it's not necessary atm*)
Lemma adde_EList1_new:
  ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList EdgeListGG_adde).
Proof.
intros.
unfold EdgeListGG_adde. simpl. unfold pregraph_add_edge.
set (l:=(u,v)::EList g). unfold EList. destruct finiteE. simpl.
destruct a. unfold addValidFunc in H1. simpl in H1.
apply NoDup_Permutation. unfold l. apply NoDup_cons. rewrite EList_evalid. auto. apply NoDup_EList. auto.
intros; split; intros. apply H1. destruct H2. right; auto. left. rewrite <- EList_evalid. apply H2.
apply H1 in H2. unfold l. destruct H2.
right. apply EList_evalid. auto.
left. auto.
Qed.

Lemma adde_EList2:
  forall e', In e' (EList g) -> In e' (EList EdgeListGG_adde).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
unfold EdgeListGG_adde in H1. simpl in H1. unfold addValidFunc in H1. apply H1.
left. apply EList_evalid in H. apply H.
Qed.

Lemma adde_elabel1:
  elabel EdgeListGG_adde (u,v) = w.
Proof.
simpl. unfold update_elabel. unfold equiv_dec. destruct E_EqDec. auto.
unfold complement in c. unfold equiv in c. contradiction.
Qed.

Lemma adde_evalid_or:
  forall e', evalid EdgeListGG_adde e' -> (evalid g e' \/ e' = (u,v)).
Proof. unfold EdgeListGG_adde; simpl; unfold addValidFunc. intros. apply H. Qed.

Lemma adde_EList_rev:
  forall l, ~ evalid g (u,v) ->
    Permutation ((u,v)::l) (EList EdgeListGG_adde) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList EdgeListGG_adde)).
apply (Permutation_in (l:=(u,v)::l)). auto. right; auto.
apply EList_evalid in H2. apply adde_evalid_or in H2. destruct H2.
rewrite EList_evalid; auto.
subst x. assert (NoDup ((u,v)::l)). apply NoDup_Perm_EList in H0; auto.
apply NoDup_cons_2 in H2. contradiction.
destruct (E_EqDec x (u,v)). unfold equiv in e. subst x. apply EList_evalid in H1; contradiction.
unfold complement, equiv in c.
apply adde_EList2 in H1.
apply (Permutation_in (l':=(u,v)::l)) in H1. destruct H1. symmetry in H1; contradiction. auto.
apply Permutation_sym; auto.
Qed.

Lemma adde_g2wedgelist_1:
  In (w, (u,v)) (graph_to_wedgelist EdgeListGG_adde).
Proof.
intros. unfold graph_to_wedgelist. unfold edge_to_wedge.
replace (w, (u,v)) with (edge_to_wedge EdgeListGG_adde (u,v)).
apply in_map. apply EList_evalid. apply add_edge_evalid.
unfold edge_to_wedge. rewrite adde_elabel1. auto.
Qed.

Corollary adde_g2wedgelist_2:
  forall e', (u,v)<>e' -> evalid g e' -> In (elabel g e', e') (graph_to_wedgelist EdgeListGG_adde).
Proof.
intros. unfold graph_to_wedgelist. replace (elabel g e', e') with (edge_to_wedge EdgeListGG_adde e').
apply in_map. apply EList_evalid. apply add_edge_preserves_evalid; auto.
unfold edge_to_wedge; simpl. unfold update_elabel.
unfold equiv_dec. destruct E_EqDec. contradiction. auto.
Qed.

Lemma adde_numE:
  ~ evalid g (u,v) -> numE EdgeListGG_adde = numE g + 1.
Proof.
intros. unfold numE.
pose proof (adde_EList1_new H).
replace (Zlength (EList EdgeListGG_adde)) with (Zlength ((u,v)::EList g)).
apply Zlength_cons. apply Permutation_Zlength; auto.
Qed.

End EdgeListGG_add.

(*****************************REMOVE EDGES****************************)

Section EdgeListGG_eremove.

Context {g: EdgeListGG}.
Context {e: EType}.
Context {e_evalid: evalid g e}. (*Idk if remove_edge cares, but it matters for all uses here*)

Definition EdgeListLG_eremove :=
  @Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG (pregraph_remove_edge g e)
  (vlabel g)
  (*(fun e0 => if eq_dec e0 e then ? else elabel g e )*) (elabel g)
  (glabel g).

(*there is a clash with pregraph_remove_edge_finite*)
Instance Sound_EdgeListLG_eremove :
  SoundEdgeList EdgeListLG_eremove.
Proof.
constructor.
+auto.
+simpl; intros; rewrite vertex_valid. split; auto.
+simpl; unfold removeValidFunc; intros. destruct H.
apply evalid_strong_evalid in H. apply H.
+simpl; unfold removeValidFunc; intros. destruct H.
apply weight_valid in H; auto.
+simpl; unfold removeValidFunc; intros. destruct H.
apply src_fst; auto.
+simpl; unfold removeValidFunc; intros. destruct H.
apply dst_snd; auto.
+constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
destruct (in_dec E_EqDec e (EList g)).
(*case e already inside*)
exists (remove E_EqDec e (EList (g))). split.
apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff. rewrite EList_evalid. split; auto.
(*case e not inside*)
exists (EList g). split. apply NoDup_EList.
intros; split; intros. split. apply EList_evalid in H; auto.
unfold not; intros; subst x. contradiction.
destruct H. apply EList_evalid. auto.
Qed.

Definition EdgeListGG_eremove: EdgeListGG :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG SoundEdgeList
    (EdgeListLG_LabeledGraph EdgeListLG_eremove)
    Sound_EdgeListLG_eremove.

Lemma eremove_vvalid:
  forall v, vvalid EdgeListGG_eremove v <-> vvalid g v.
Proof.
simpl. intros; split; auto.
Qed.

(*Don't bother with defining what happens when e isn't inside*)
Lemma eremove_evalid1:
  ~ evalid EdgeListGG_eremove e.
Proof.
simpl. unfold removeValidFunc, not; intros. destruct H. contradiction.
Qed.

Lemma eremove_EList_rev:
  forall l, Permutation l (EList EdgeListGG_eremove) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList EdgeListGG_eremove)).
rewrite EList_evalid. apply eremove_evalid1.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList EdgeListGG_eremove))) in H1. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H2. subst x. auto.
apply (Permutation_in (l':= (EList EdgeListGG_eremove))) in H2; auto.
rewrite EList_evalid in H2. simpl in H2. unfold removeValidFunc in H2. apply H2.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid EdgeListGG_eremove x).
apply remove_edge_evalid. split. apply EList_evalid in H2; auto. auto.
rewrite <- EList_evalid in H3.
apply (Permutation_in (l:= (EList EdgeListGG_eremove))). apply Permutation_sym; auto. apply H3.
Qed.

Lemma eremove_uforest':
  uforest' g -> uforest' EdgeListGG_eremove /\ ~ connected EdgeListGG_eremove (src g e) (dst g e).
Proof.
intros.
destruct e as (u,v) eqn:X. rewrite src_fst, dst_snd; auto.
pose proof eremove_evalid1.
assert (Hvvalid: forall v1 : VType, vvalid EdgeListGG_eremove v1 <-> vvalid g v1).
  simpl; intros; split; auto.
split.
{ split. intros. simpl. apply H. apply H1.
split. intros. unfold adj_edge, strong_evalid in H1; simpl in H1.
  unfold removeValidFunc in H1. destruct H1. destruct H1. destruct H2.
  destruct H. destruct H5. apply (H5 u0 v0).
  split; split.
  split. apply H1. apply H1. apply H3.
  split. apply H2. apply H2. apply H4.
split. intros. apply evalid_strong_evalid; auto.
unfold unique_simple_upath; intros.
assert (exists l, fits_upath EdgeListGG_eremove l p1). apply valid_upath_exists_list_edges. apply H2.
destruct H5 as [l1 ?].
assert (exists l, fits_upath EdgeListGG_eremove l p2). apply valid_upath_exists_list_edges. apply H4.
destruct H6 as [l2 ?].
destruct (in_dec E_EqDec e l1).
apply (fits_upath_evalid EdgeListGG_eremove p1) in i; auto. contradiction.
destruct (in_dec E_EqDec e l2).
apply (fits_upath_evalid EdgeListGG_eremove p2) in i; auto. contradiction.
apply (fits_upath_transfer' p1 l1 _ g) in H5; auto.
apply (fits_upath_transfer' p2 l2 _ g) in H6; auto.
assert (valid_upath g p1). apply valid_upath_exists_list_edges'. exists l1. auto.
assert (valid_upath g p2). apply valid_upath_exists_list_edges'. exists l2. auto.
assert (unique_simple_upath g). apply H. unfold unique_simple_upath in H9.
destruct H1. destruct H3. destruct H2. destruct H4.
apply (H9 u0 v0 p1 p2). split; auto. split; auto. split; auto. split; auto.
intros. apply (fits_upath_evalid _ _ _ _ H6) in H7. apply H7.
intros. apply (fits_upath_evalid _ _ _ _ H5) in H7. apply H7.
}
{
unfold not, connected; intros.
destruct H1 as [p ?].
assert (exists l, fits_upath EdgeListGG_eremove l p). apply valid_upath_exists_list_edges. apply H1.
destruct H2 as [l ?].
assert (fits_upath g l p). apply (sound_fits_upath_transfer p l EdgeListGG_eremove g); auto.
intros. apply (fits_upath_evalid _ _ _ _ H2) in H3. apply H3.
assert (connected_by_path g p u v). split.
apply valid_upath_exists_list_edges'. exists l; auto. destruct H1. auto.
pose proof (forest_bridge1 g u v H e_evalid).
assert (In (u,v) l). unfold bridge in H5. apply (H5 p l); auto.
apply (fits_upath_evalid _ _ _ _ H2) in H6. rewrite X in *. contradiction.
}
Qed.

End EdgeListGG_eremove.

(******************SORTING****************)

(*Sigh, this is really silly, but I need a sort for this specific "struct"*)
Fixpoint insert (g:EdgeListGG) (i:EType) (l: list EType) :=
  match l with
  | nil => i::nil
  | h::t => if (elabel g i <=? elabel g h) then i::h::t else h :: insert g i t
 end.

Fixpoint sort (g: EdgeListGG) (l: list EType) :=
  match l with
  | nil => nil
  | h::t => insert g h (sort g t)
end.

Inductive sorted (g: EdgeListGG): list EType -> Prop := 
| sorted_nil:
    sorted g nil
| sorted_1: forall x,
    sorted g (x::nil)
| sorted_cons: forall x y l,
     (elabel g x) <= (elabel g y) -> sorted g (y::l) -> sorted g (x::y::l).

Lemma insert_perm: forall (g: EdgeListGG) x l, Permutation (x::l) (insert g x l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. destruct (Z.leb (elabel g x) (elabel g a)). apply Permutation_refl.
apply (Permutation_trans (l':=a::x::l)). apply perm_swap.
apply perm_skip. apply IHl.
Qed.

Theorem sort_perm: forall (g: EdgeListGG) l, Permutation l (sort g l).
Proof.
induction l. simpl. apply Permutation_refl.
simpl. apply (Permutation_trans (l':=a::(sort g l))).
apply perm_skip. apply IHl.
apply insert_perm.
Qed.

Lemma insert_sorted:
  forall g a l, sorted g l -> sorted g (insert g a l).
Proof.
intros. induction H.
simpl. apply sorted_1.
simpl. destruct (Z.leb (elabel g a) (elabel g x)) eqn:ax.
apply sorted_cons. apply Z.leb_le. auto. apply sorted_1.
apply Z.leb_gt in ax. apply sorted_cons. lia. apply sorted_1.
simpl.
destruct (Z.leb (elabel g a) (elabel g x)) eqn:ax.
apply sorted_cons. apply Z.leb_le. auto. apply sorted_cons; auto.
apply Z.leb_gt in ax. simpl in IHsorted. destruct (Z.leb (elabel g a) (elabel g y)) eqn:ay.
apply sorted_cons. lia. apply Z.leb_le in ay. apply sorted_cons; auto.
apply Z.leb_gt in ay. apply sorted_cons. lia. apply IHsorted.
Qed.

Theorem sort_sorted: forall (g:EdgeListGG) (l: list EType), sorted g (sort g l).
Proof.
induction l; intros. apply sorted_nil.
destruct l. simpl. apply sorted_1.
simpl in IHl. simpl. apply insert_sorted. auto.
Qed.

Definition sorted' (g: EdgeListGG) (l: list EType) :=
 forall i j, 0 <= i < j -> j < Zlength l -> Z.le (elabel g (Znth i l)) (elabel g (Znth j l)).

Lemma sorted_sorted':
  forall g l, sorted g l -> sorted' g l.
Proof.
intros. unfold sorted'. induction H.
intros. rewrite Zlength_nil in H0. lia.
intros. rewrite Zlength_cons, Zlength_nil in H0. lia.
intros. destruct (Z.lt_trichotomy i 0). lia. destruct H3.
subst i. rewrite Znth_0_cons. rewrite Znth_pos_cons by lia.
destruct (Z.lt_trichotomy (j-1) 0). lia. destruct H3.
rewrite H3. rewrite Znth_0_cons. auto.
specialize IHsorted with 0 (j-1). rewrite Znth_0_cons in IHsorted.
apply (Z.le_trans (elabel g x) (elabel g y)). auto. apply IHsorted. lia.
rewrite Zlength_cons in H2. lia.
rewrite (Znth_pos_cons i) by lia. rewrite (Znth_pos_cons j) by lia. apply IHsorted.
lia. rewrite Zlength_cons in H2. lia.
Qed.

End EdgeListModel.
