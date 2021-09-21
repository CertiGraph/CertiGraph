Require Import CertiGraph.unionfind.env_unionfind_arr.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.UnionFind.
Require Import CertiGraph.msl_application.ArrayGraph.
Require Import CertiGraph.floyd_ext.share.
Require Import VST.floyd.library.
Require Import CertiGraph.unionfind.spatial_array_graph.

Local Coercion UFGraph_LGraph: UFGraph >-> LGraph.
Local Identity Coercion ULGraph_LGraph: LGraph >-> UnionFindGraph.LGraph.
Local Identity Coercion LGraph_LabeledGraph: UnionFindGraph.LGraph >-> LabeledGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.
Existing Instances maGraph finGraph liGraph.

Local Open Scope Z_scope.

(*There is a full definition in the verified malloc, but it's impl-specific*)
(*Parameter malloc_token': share -> Z -> val -> mpred.*)

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh:share, n: Z(*, gv:globals*)
  PRE [tint]
     PROP (writable_share sh;
            4 <= n <= Int.max_unsigned
          )
     PARAMS (Vint (Int.repr n))
     GLOBALS ((*gv*))
     SEP (
          )
  POST [ tptr tvoid ]
     EX v: pointer_val,
     PROP (malloc_compatible n (pointer_val_val v))
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (
          memory_block sh n (pointer_val_val v)
         ).
(*
Definition mallocK_spec :=
 DECLARE _mallocK
  WITH gv: globals, sh: share, n: Z
  PRE [tint]
     PROP (writable_share sh;
           4 <= n <= Ptrofs.max_unsigned - 12 (*we don't want to malloc 0. The 12 is just some constant from the verified malloc*)
          )
     PARAMS (Vptrofs (Ptrofs.repr n))
     GLOBALS (gv)
     SEP (mem_mgr gv)
  POST [ tptr tvoid ]
     EX v: _,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (mem_mgr gv; malloc_token' sh n v; memory_block sh n v).
*)
(*Basically collapses everything into the mpred defined by SAG_VST
takes in a lst of rank-parent pairs(from where? g?)
  which is converted into the Cdata structures
sh is the only parameter needed
data_at sh (tarray vertex_type (Z.of_nat (length lst)))
                               (map vgamma2cdata lst) (pointer_val_val x)
*)
Definition whole_graph sh g x :=
  (@full_graph_at mpred SAGA_VST pointer_val (SAG_VST sh) g x).

Definition makeSet_spec :=
  DECLARE _makeSet
  WITH gv:globals, sh: share, V: Z
    PRE [tint]
      PROP (writable_share sh; readable_share sh;
            0 < V <= Int.max_signed / 8)
      PARAMS (Vint (Int.repr V))
      GLOBALS ()
      SEP ((*mem_mgr gv*))
    POST [tptr vertex_type]
      EX rt: pointer_val, (*creates a graph where*)
      PROP (forall i: Z, 0 <= i < V -> vvalid (makeSet_discrete_Graph (Z.to_nat V)) i) (*anything between 0 and V is a vertex*)
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (
           (*mem_mgr gv; malloc_token' sh (V*4) (pointer_val_val rt);*)
           whole_graph sh (makeSet_discrete_Graph (Z.to_nat V)) rt). (*representation in heap...*)

Definition freeSet_spec :=
  DECLARE _freeSet
  WITH sh: share, p: pointer_val, g: ArrayGraph.UFGraph(*, gv: globals*)
    PRE [tptr vertex_type]
    PROP () PARAMS ((pointer_val_val p)) GLOBALS ((*gv*))
    SEP ((*mem_mgr gv;
          malloc_token' sh (Z.of_nat (numV' g)) (pointer_val_val p);*)
          whole_graph sh g p)
  POST [tvoid]
    PROP () LOCAL () SEP ((*mem_mgr gv*)).

Definition find_spec :=
  DECLARE _find
  WITH sh: share, g: UFGraph, subsets: pointer_val, i: Z
    PRE [tptr vertex_type, tint]
      PROP (writable_share sh; vvalid g i)
      PARAMS (pointer_val_val subsets; Vint (Int.repr i))
      GLOBALS ()
      SEP (whole_graph sh g subsets)
    POST [tint]
      EX g': UFGraph, EX rt: Z,
      PROP (uf_equiv g g' ; uf_root g' i rt)
      LOCAL (temp ret_temp (Vint (Int.repr rt)))
      SEP (whole_graph sh g' subsets).

Definition union_spec :=
 DECLARE _Union
  WITH sh: share, g: UFGraph, subsets: pointer_val, x: Z, y: Z
  PRE [tptr vertex_type, tint, tint]
          PROP  (writable_share sh; vvalid g x; vvalid g y)
          PARAMS (pointer_val_val subsets; Vint (Int.repr x); Vint (Int.repr y))
          GLOBALS ()
          SEP   (whole_graph sh g subsets)
  POST [ Tvoid ]
        EX g': UFGraph,
        PROP (uf_union g x y g')
        LOCAL ()
        SEP (whole_graph sh g' subsets).
