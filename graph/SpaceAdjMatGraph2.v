Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.exportclight.Clightdefs.

Require Import VST.veric.expr.
Require Import VST.veric.mpred.
Require Import VST.floyd.forward.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.
Require Import VST.floyd.coqlib3.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.seplog.

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.MathAdjMatGraph.

Section SpaceAdjMatGraph2.

  Context {size : Z}. 
  
  
  (* SPATIAL REPRESENTATION *)

  (* Assumption: (v,0), (v,1) ... (v, size-1) are edges.
   Action: makes a list containing each edge's elabel.
   The argument f is an opportunity to tweak the edges as needed
   *)  
  Definition vert_to_list (g: AdjMatLG) (f : E -> E) (v : V) :=
    map (elabel g)
        (map (fun x => f (v,x))
             (nat_inc_list (Z.to_nat size))).

  (* Assumptions: 
   1. 0, 1, ... (size-1) are vertices
   2. for any vertex v,
          (v,0), (v,1) ... (v, size-1) are edges.
          
      Action:
      Makes a list of lists, where each member list 
      is a vertex's edge-label-list (see helper above).
   *)
  Definition graph_to_mat (g: AdjMatLG) (f : E -> E) : list (list Z) :=
    map (vert_to_list g f)
        (nat_inc_list (Z.to_nat size)).

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

   Lemma Zlength_concat:
   forall size n f,
     0 <= size ->
     0 <= n ->
     Forall (fun list : list Z => Zlength list = n)
            (map f (nat_inc_list (Z.to_nat size))) ->
     Zlength (concat (map f (nat_inc_list (Z.to_nat size)))) =
     Z.of_nat (Z.to_nat size) * n.
 Proof.
   intros.
   induction (Z.to_nat size0).
   1: simpl; apply Zlength_nil.
   rewrite Nat2Z.inj_succ, Z.mul_succ_l.
   simpl. rewrite map_app, concat_app, Zlength_app.
   simpl. rewrite app_nil_r.
   f_equal.
   - apply IHn0.
     rewrite Forall_forall in H1 |- *.
     intros. apply H1.
     simpl. rewrite map_app.
     apply in_or_app; left; trivial.
   - rewrite Forall_forall in H1. apply H1.
     apply in_map. rewrite nat_inc_list_in_iff. lia.
 Qed.

 Lemma graph_to_list_Zlength:
    forall g (f : E -> E) n,
      0 <= size ->
      0 <= n ->
      Forall (fun list => Zlength list = n) (graph_to_mat g f) ->
      Zlength (graph_to_list g f) = size * n.
  Proof.
    intros.
    rewrite <- (Z2Nat.id size); trivial.
    unfold graph_to_list, graph_to_mat in *.
    apply Zlength_concat; trivial.
  Qed.

  Definition SpaceAdjMatGraph' sh (cs: compspecs) (f : E -> E) g_contents gaddr : mpred :=
    data_at sh (tarray tint (size * size))
            (map Vint (map Int.repr g_contents))
            gaddr.

  Definition SpaceAdjMatGraph sh (cs: compspecs) (f : E -> E) g gaddr : mpred :=
    SpaceAdjMatGraph' sh cs f (graph_to_list g f) gaddr.

(*
  The below is not currently used by SpaceDijkGraph because 
  iter_sepcon is cleaner. However, just keep it around 
  because it is a general model.
  For a (better?) example of this in use for VST, see above.
 *)

(* 
  What it does:        
  Uses abstract_data_at to create a spatial representation.
 *)
  Class SpaceAdjMatGraph_abstract (Addr: Type) (Pred: Type) :=
    abstract_data_at: Addr -> list Z -> Pred.
  
  Context {Pred: Type}.
  Context {Addr: Type}.
  Context {SAMG : SpaceAdjMatGraph_abstract Addr Pred}.
  
  Definition AdjMatGraph_rep
             (g: AdjMatLG)
             (f : E -> E)
             (a : Addr) : Pred :=
    abstract_data_at a (@graph_to_list g f).
  
End SpaceAdjMatGraph2.

(* Lemma Zlength_concat: *)
  (* forall  *)

Lemma graph_to_list_to_mat:
  forall {size} g (f : E -> E) u i,
    0 <= u < size ->
    0 <= i < size ->
    0 < size ->
    Forall (fun list => Zlength list = size)
           (@graph_to_mat size g f) ->
    Znth (u * size + i) (@graph_to_list size g f) =
    Znth i (Znth u (@graph_to_mat size g f)).
Proof.
  intros.
  assert (Htemp: 0 <= size) by lia.
  clear Htemp.
  unfold graph_to_list, graph_to_mat in *.
  induction (Z.to_nat size).
  1: { admit. }
  simpl.
  rewrite map_app, concat_app.
  destruct (Coqlib.zlt u (Z.of_nat n)).
  - repeat rewrite app_Znth1.
    + apply IHn.
      rewrite Forall_forall in H2 |- *.
      intros. apply H2. simpl. rewrite map_app.
      apply in_or_app. left; trivial.
    + rewrite Zlength_map, nat_inc_list_Zlength; lia.
    + rewrite Zlength_concat

      unfold vert_to_list.
      admit.
  - repeat rewrite app_Znth2.
    + rewrite Zlength_map, nat_inc_list_Zlength.
      simpl. rewrite app_nil_r.
      admit.
    + rewrite Zlength_map, nat_inc_list_Zlength; lia.
    + admit.
Admitted.
