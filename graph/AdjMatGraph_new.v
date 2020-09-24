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

Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.path_lemmas.


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
  
  Class SoundAdjMat (g: AdjMatLG) :=
    {
    sr: (* size_representable *)
      0 < size <= Int.max_signed;
    ir: (* inf_representable *)
      0 <= inf <= Int.max_signed; 
    vm: (* vvalid_meaning *)
      forall v, vvalid g v <-> 0 <= v < size;
    em: (* evalid_meaning *)
      forall e, evalid g e <-> 
                Int.min_signed <= elabel g e <= Int.max_signed /\
                elabel g e <> inf;
    iew: (* invalid_edge_weight *)
      forall e, ~ evalid g e <-> elabel g e = inf;
    esf: (* edge_src_fst *)
      forall e, src g e = fst e;
    eds: (* edge_dst_snd *)
      forall e, dst g e = snd e;
    fin:
      FiniteGraph g
    }.
  
  (* example of how to instantiate *)
  Definition AdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundAdjMat g)).
  (* Clients may want to further restrict the 
     soundness condition and then use that restricted version. *)

  (* Getters for the plugins *)

  Definition size_representable (g: AdjMatGG) :=
    @sr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition inf_representable (g: AdjMatGG) :=
    @ir g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition vvalid_meaning (g: AdjMatGG) :=
    @vm g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_meaning (g: AdjMatGG) :=
    @em g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition invalid_edge_weight (g: AdjMatGG) :=
    @iew g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_src_fst (g: AdjMatGG) :=
    @esf g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_dst_snd (g: AdjMatGG) :=
    @eds g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition finGraph (g: AdjMatGG) :=
    @fin g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  (* Some lemmas from the above soundness plugins *)
  
  Lemma valid_path_app_cons:
    forall (g: AdjMatGG) src links2u u i,
      valid_path g (src, links2u) ->
      pfoot g (src, links2u) = u ->
      strong_evalid g (u,i) ->
      valid_path g (src, links2u +:: (u,i)).
  Proof.
    intros.
    apply valid_path_app.
    split; [assumption|].
    simpl; split; trivial.
    destruct H1.
    rewrite (edge_src_fst g); simpl; assumption.
  Qed.
  
  Lemma path_ends_app_cons:
    forall (g: AdjMatGG) a b c a' a2b,
      a = a' ->
      path_ends g (a, a2b) a b ->
      path_ends g (a, a2b +:: (b, c)) a' c.
  Proof.
    split; trivial.
    rewrite pfoot_last.
    rewrite (edge_dst_snd g); trivial.
  Qed.
  
  Lemma step_in_range:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (fst x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [? _]].
    rewrite <- (edge_src_fst g); trivial.
  Qed.
  
  Lemma step_in_range2:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (snd x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [_ ?]].
    rewrite <- (edge_dst_snd g); trivial.
  Qed.

  (*ASDF: This works here*)
  Definition edgeless_lgraph2: AdjMatLG :=
  @Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
    (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
    (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)
  
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

