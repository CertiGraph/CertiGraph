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
Require Import CertiGraph.graph.MathEdgeLabelGraph.

Section Spatial_Edge_Labeled_Graph_Model_1.
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
     (v,d1,0), (v,d2,1) ... (v, dn, m) are edges.
     v is the source vertex, 
     d1...dn are the (repeatable) destinations,
     and the numbers 0...m are the out-vertex index numbers
     
     Action: 
      Makes a list containing each edge's elabel.
      The argument f is an opportunity to tweak the edges as needed
   *)  
  Definition vert_to_list (g: EdgeLabLG) (f : E -> E) (v : V) :=
    map (elabel g)
        (map f (combine
                  (map (fun x => (v,x)) (vlabel g v))
                  (nat_inc_list (length (vlabel g v))))).
  
  (* Assumptions: 
     1. 0, 1, ... (size-1) are vertices
     2. the assumptions from the helper above hold for each vertex
          
     Action:
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
   *)
  Definition graph_to_mat (g: EdgeLabLG) (f : E -> E) : list (list Z) :=
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

  Lemma combine_Znth:
    forall {A B : Type}
           {I: Inhabitant A}
           {I: Inhabitant B}
           (l : list A) (l' : list B) (n : Z),
      length l = length l' ->
      0 <= n < Zlength l ->
      Znth n (combine l l') = (Znth n l, Znth n l').
  Proof.
    intros.
    repeat rewrite <- nth_Znth.
    all: 
      rewrite Zlength_correct in *;
      try rewrite combine_length;
      try rewrite <- H;
      try rewrite Nat.min_id; trivial.
    apply combine_nth; trivial.
  Qed.
        
  Lemma elabel_Znth_graph_to_mat:
    forall (g: @EdgeLabGG size) (f: E -> E) src dst out,
      evalid g (src, dst, out) ->
      elabel g (f (src, dst, out)) =
      Znth out (Znth src (graph_to_mat g f)).
  Proof.
    intros.
    assert (vvalid g src). {
      apply (evalid_strong_evalid g) in H.
      destruct H as [_ [? _]].
      rewrite edge_src_fst in H; apply H.
    }
    rewrite (vvalid_meaning g) in H0.
    rewrite (evalid_meaning g) in H; destruct H as [_ [ ??]].
    assert (0 <= size). {
      pose proof (size_representable g). lia.
    }
    unfold graph_to_mat.
    rewrite Znth_map, nat_inc_list_i.
    unfold vert_to_list. rewrite Znth_map.
    rewrite Znth_map. f_equal. f_equal.
    rewrite (combine_Znth
               (map (fun x : V => (src, x)) _ )
               (nat_inc_list _) _).
    rewrite nat_inc_list_i, Znth_map, H1; trivial.

    rewrite <- Zlength_correct; trivial.
    rewrite map_length, nat_inc_list_length; trivial.
    rewrite Zlength_map; trivial.
    2: rewrite Zlength_map.

    1,2: rewrite Zlength_correct in *;
      rewrite (combine_length
                 (map (fun x : V => (src, x)) _ )
                 (nat_inc_list _)),
      map_length, nat_inc_list_length, Nat.min_id; trivial.
    2: rewrite nat_inc_list_Zlength.
    1,2: rewrite Z2Nat.id; trivial.
  Qed.
  
  Definition graph_to_list (g: EdgeLabLG) (f : E -> E) : list Z :=
    (concat (graph_to_mat g f)).

  (*

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

*)
End Spatial_Edge_Labeled_Graph_Model_1.
