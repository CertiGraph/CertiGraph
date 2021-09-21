Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.exportclight.Clightdefs.

Require Import VST.veric.mpred.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.
Require Import VST.floyd.coqlib3.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.seplog.

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.MathAdjMatGraph.

Section Spatial_AdjMat_Model_1.
  (* Model 1 is for a heap-allocated graph,
     where the graph is malloc-ed
     by first malloc-ing a "spine" column of some size, 
     and then malloc-ing a "row" into each cell
     of the spine.       
   *)

  Context {size : Z}. 
  Context {CompSpecs : compspecs}.
  Context {V_EqDec : EquivDec.EqDec V eq}. 
  Context {E_EqDec: EquivDec.EqDec E eq}.
  
  (* Assumption: 
     (v,0), (v,1) ... (v, size-1) are edges.
     
     Action: 
      Makes a list containing each edge's elabel.
      The argument f is an opportunity to tweak the edges as needed
   *)  
  Definition vert_to_list (g: AdjMatLG) (f : E -> E) (v : V) :=
    map (elabel g)
        (map (fun x => f (v,x))
             (nat_inc_list (Z.to_nat size))).

  (* Assumptions: 
     1. 0, 1, ... (size-1) are vertices
     2. for any vertex v, (v,0), (v,1) ... (v, size-1) are edges.
          
     Action:
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
   *)
  Definition graph_to_mat (g: AdjMatLG) (f : E -> E) : list (list Z) :=
    map (vert_to_list g f)
        (nat_inc_list (Z.to_nat size)).

  (* Some lemmas about the above *)
  
  Lemma graph_to_mat_Zlength:
    forall g (f : E -> E),
      0 <= size ->
      Zlength (graph_to_mat g f) = size.
  Proof.
    intros. unfold graph_to_mat.
    rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; trivial.
  Qed.

  Lemma elabel_Znth_graph_to_mat:
    forall (g: AdjMatLG) (f: E -> E) src dst,
      0 <= size ->
      0 <= src < size ->
      0 <= dst < size ->
      elabel g (f (src, dst)) =
      Znth dst (Znth src (graph_to_mat g f)).
  Proof.
    intros. 
    unfold graph_to_mat.
    rewrite Znth_map, nat_inc_list_i.
    unfold vert_to_list. rewrite Znth_map.
    rewrite Znth_map. rewrite nat_inc_list_i.
    reflexivity.
    3: rewrite Zlength_map.
    2, 3, 5: rewrite nat_inc_list_Zlength.
    all: rewrite Z2Nat.id; trivial.
  Qed.
  
  Definition graph_to_list (g: AdjMatLG) (f : E -> E) : list Z :=
    (concat (graph_to_mat g f)).

  Definition list_address addresses index : val :=
    Znth index addresses.

  Definition list_rep sh addresses contents_mat index :=
    let mylist := (Znth index contents_mat) in
    data_at sh (tarray tint size)
            (map Vint (map Int.repr mylist))
            (list_address addresses index).

  Definition SpaceAdjMatGraph' sh g_contents (g_ptr: val) (addresses : list val) : mpred :=
    sepcon (iter_sepcon (list_rep sh addresses g_contents)
                        (nat_inc_list (Z.to_nat size)))
           (data_at sh (tarray (tptr tint) size) addresses g_ptr).

  Definition SpaceAdjMatGraph sh (f : E -> E) g (g_ptr: val) (addresses : list val) : mpred :=
    SpaceAdjMatGraph' sh (graph_to_mat g f) g_ptr addresses.
                
  Lemma SpaceAdjMatGraph_unfold': forall sh g_contents (g_ptr : val) (addresses : list val) i,
      Zlength g_contents = size ->
      0 <= i < size ->
      SpaceAdjMatGraph' sh g_contents g_ptr addresses =
      sepcon
        (sepcon (iter_sepcon (list_rep sh addresses g_contents)
                             (sublist 0 i (nat_inc_list (Z.to_nat size))))
                (sepcon
                   (list_rep sh addresses g_contents i)
                   (iter_sepcon (list_rep sh addresses g_contents)
                                (sublist (i + 1) (Zlength g_contents) (nat_inc_list (Z.to_nat size))))))
        (data_at sh (tarray (tptr tint) size) addresses g_ptr).
  Proof.
    intros. unfold SpaceAdjMatGraph'.
    replace (nat_inc_list (Z.to_nat size)) with
        (sublist 0 size (nat_inc_list (Z.to_nat size))) at 1.
    2: rewrite sublist_same; trivial; rewrite nat_inc_list_Zlength; lia.
    rewrite (sublist_split 0 i size),
    (sublist_split i (i+1) size), (sublist_one i); try lia.
    2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
    rewrite nat_inc_list_i.
    2: rewrite Z2Nat_id', Z.max_r; lia.
    repeat rewrite iter_sepcon_app.
    simpl. rewrite sepcon_emp. rewrite H.
    reflexivity.
  Qed.

  Lemma SpaceAdjMatGraph_unfold: forall sh (f : E -> E) g (g_ptr : val) (addresses : list val) i,
      let contents := (graph_to_mat g f) in 
      0 <= i < size ->
      SpaceAdjMatGraph sh f g g_ptr addresses =
      sepcon
        (sepcon (iter_sepcon (list_rep sh addresses contents)
                             (sublist 0 i (nat_inc_list (Z.to_nat size))))
                (sepcon
                   (list_rep sh addresses contents i)
                   (iter_sepcon (list_rep sh addresses contents)
                                (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat size))))))
        (data_at sh (tarray (tptr tint) size) addresses g_ptr).
  Proof.
    intros. apply SpaceAdjMatGraph_unfold'; trivial.
    subst contents. rewrite graph_to_mat_Zlength; lia.
  Qed.

End Spatial_AdjMat_Model_1.
