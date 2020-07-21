Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.ZArith_dec.
Require Import Coq.ZArith.Zcomplements.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Znat.

Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.exportclight.Clightdefs.

Require Import VST.veric.val_lemmas.
Require Import VST.veric.expr.
Require Import VST.veric.mpred.
Require Import VST.floyd.forward.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.
Require Import VST.floyd.coqlib3.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.seplog.

Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.graph.FiniteGraph.

(*
  AdjMat wishlist
  0. some distinguished inf value
  1. V: Z, E: Z, Elabel: Z
  2. forall e, ensure elabel is reppable
  3. forall e, evalid e -> elabel e < inf
  4. etc... soundness
  5. vert to list function
  6. graph to mat function 
  7. graph_rep (graph -> mpred)
  8. graph_unfold
 *)

Section AdjMatGraph.

  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

  Local Open Scope Z_scope.

  (* Most of the types are constrained because 
     we want easy AdjMat representation. *)
  Definition V : Type := Z.
  Definition E : Type := Z * Z.
  Definition DV: Type := unit.
  Definition DE : Type := Z. 
  Definition DG: Type := unit.

  Instance V_EqDec : EqDec V eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

  Instance E_EqDec: EqDec E eq.
  Proof.
    hnf. intros [x] [y].
    destruct (equiv_dec x y).
    - hnf in e. destruct (Z.eq_dec z z0); subst.
      + left; reflexivity.
      + right. intro. apply n. inversion H. reflexivity.
    - right; intro; apply c; inversion H; reflexivity.
  Defined.

  Definition AdjMatLG := (@LabeledGraph V E _ _ DV DE DG).
  (* This is the basic LabeledGraph for all our AdjMat representations.
   We need some further restrictions, which we will place 
   in the GeneralGraph's soundness condition.  
   *)

  (* The instantiator will have to supply a max number of vertices
   and a special "infinity" value to indicate unreachability 
   *)
  Context {size : Z}. 
  Context {inf : Z}.
  
  Class AdjMatSoundness (g: AdjMatLG) :=
    {
    size_representable:
      0 <= size <= Int.max_signed;
    inf_representable:
      0 <= inf <= Int.max_signed; 
    vert_representable:
      forall v, vvalid g v ->
                0 <= v < size;
    edge_src_dst_valid:
      forall e, evalid g e ->
                vvalid g (src g e) /\ vvalid g (dst g e);
    edge_weight_representable:
      forall e, evalid g e ->
                Int.min_signed <= elabel g e <= Int.max_signed;
    edge_weight_not_inf:
      forall e, evalid g e ->
                elabel g e <> inf;
    edge_weight_invalid:
      forall e, ~ evalid g e ->
                elabel g e = inf;
    edge_src_fst:
      forall e, evalid g e -> src g = fst;
    edge_dst_snd:
      forall e, evalid g e -> dst g = snd;
    fin:
      FiniteGraph g
    }.

  (* example of how to instantiate *)
  Definition AdjMatGG := (GeneralGraph V E DV DE DG (fun g => AdjMatSoundness g)).
  (* Clients may want to further restrict the soundness condition and then 
   use that restricted version. *)


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

  Definition inrange_graph_gen g (f: E -> E) :=
    let grph_contents := (graph_to_mat g f) in
    forall i j,
      0 <= i < Zlength grph_contents ->
      0 <= j < Zlength grph_contents ->
      0 <= Znth i (Znth j grph_contents) <= Int.max_signed \/
      Znth i (Znth j grph_contents) = inf.
  (* grr hate this, will massage away.
     Even if it is needed, it is a LEMMA using Soundness
     and not a definition from axioms
   *)
  
  Definition graph_to_list (g: AdjMatLG) (f : E -> E) : list Z :=
    (concat (graph_to_mat g f)).

  Definition list_address (cs: compspecs) a index : val :=
    offset_val (index * sizeof (tarray tint size)) a.

  Definition list_rep sh (cs: compspecs) l contents_mat index :=
    let mylist := (Znth index contents_mat) in
    data_at sh (tarray tint size)
            (map Vint (map Int.repr mylist))
            (list_address cs l index).

  Definition SpaceAdjMatGraph sh (cs: compspecs) (f : E -> E) g gaddr : mpred :=
    iter_sepcon (list_rep sh cs gaddr (graph_to_mat g f))
                (nat_inc_list (Z.to_nat size)).

  Lemma SpaceAdjMatGraph_unfold: forall sh (cs: compspecs) (f : E -> E) g ptr i,
      let contents := (graph_to_mat g f) in 
      0 <= i < size ->
      SpaceAdjMatGraph sh cs f g ptr =
      sepcon (iter_sepcon (list_rep sh cs ptr contents)
                          (sublist 0 i (nat_inc_list (Z.to_nat size))))
             (sepcon
                (list_rep sh cs ptr contents i)
                (iter_sepcon (list_rep sh cs ptr contents)
                             (sublist (i + 1) (Zlength contents) (nat_inc_list (Z.to_nat size))))).
  Proof.
    intros. unfold SpaceAdjMatGraph.
    replace (nat_inc_list (Z.to_nat size)) with
        (sublist 0 size (nat_inc_list (Z.to_nat size))) at 1.
    2: rewrite sublist_same; trivial; rewrite nat_inc_list_Zlength; lia.
    rewrite (sublist_split 0 i size),
    (sublist_split i (i+1) size), (sublist_one i); try lia.
    2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
    rewrite nat_inc_list_i.
    2: rewrite Z2Nat_id', Z.max_r; lia.
    repeat rewrite iter_sepcon_app.
    simpl. rewrite sepcon_emp. subst contents.
    rewrite graph_to_mat_Zlength; trivial. lia.
  Qed.

End AdjMatGraph.


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
Context {size: Z}.

Definition AdjMatGraph_rep
           (g: AdjMatLG)
           (f : E -> E)
           (a : Addr) : Pred :=
  abstract_data_at a (@graph_to_list size g f).

