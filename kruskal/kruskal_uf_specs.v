(* TODO: Perhaps make verif_unionfind_arr use
   this file instead of its own local copy 
   of these specs?
*)

(* UF's imports (already made minimal *)
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.sample_mark.spatial_array_graph.

(* Kruskal's imports (already made minimal *)
Require Import RamifyCoq.kruskal.mst.
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.

(* UNION FIND SPECS *)

Local Open Scope Z_scope.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH sh:wshare, n: Z
  PRE [tint]
     PROP (4 <= n <= Int.max_unsigned)
     PARAMS (Vint (Int.repr n))
     GLOBALS ()
     SEP ()
  POST [ tptr tvoid ]
     EX v: pointer_val,
     PROP (malloc_compatible n (pointer_val_val v))
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (memory_block sh n (pointer_val_val v)).
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
  WITH sh: wshare, V: Z
    PRE [tint]
      PROP (0 < V <= Int.max_signed / 8)
      PARAMS (Vint (Int.repr V))
      GLOBALS ()
      SEP ()
    POST [tptr vertex_type]
      EX rt: pointer_val, (*creates a graph where*)
      PROP (forall i: Z, 0 <= i < V -> vvalid (makeSet_discrete_Graph (Z.to_nat V)) i) (*anything between 0 and V is a vertex*)
      LOCAL (temp ret_temp (pointer_val_val rt))
      SEP (whole_graph sh (makeSet_discrete_Graph (Z.to_nat V)) rt). (*representation in heap...*)

Definition find_spec :=
  DECLARE _find
  WITH sh: wshare, g: UFGraph, subsets: pointer_val, i: Z
    PRE [tptr vertex_type, tint]
      PROP (vvalid g i)
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
  WITH sh: wshare, g: UFGraph, subsets: pointer_val, x: Z, y: Z
  PRE [tptr vertex_type, tint, tint]
          PROP  (vvalid g x; vvalid g y)
          PARAMS (pointer_val_val subsets; Vint (Int.repr x); Vint (Int.repr y))
          GLOBALS ()
          SEP   (whole_graph sh g subsets)
  POST [ Tvoid ]
        EX g': UFGraph,
        PROP (uf_union g x y g')
        LOCAL ()
        SEP (whole_graph sh g' subsets).

(* KRUSKAL SPECS *)

(*Taken from VST's queue*)
Definition mallocK_spec :=
 DECLARE _mallocK
  WITH sh: wshare, n: Z
  PRE [tint]
     PROP (4 <= n <= Int.max_unsigned)
     PARAMS (Vint (Int.repr n))
     GLOBALS ()
     SEP ()
  POST [ tptr tvoid ]
     EX v: pointer_val,
     PROP (malloc_compatible n (pointer_val_val v))
     LOCAL (temp ret_temp (pointer_val_val v))
     SEP (memory_block sh n (pointer_val_val v)).

Definition free_spec :=
  DECLARE _free
  WITH h: val
    PRE [tptr tvoid]
    PROP () PARAMS (h) GLOBALS () SEP ()
  POST [tvoid]
    PROP () LOCAL () SEP ().

(*It'll be useful if we can come up with some freeN spec, then centralize these in some header*)

Definition fill_edge_spec :=
  DECLARE _fill_edge
  WITH sh: wshare, ptr: val, w: val, u: val, v: val, rubbish: reptype t_struct_edge
  PRE [tptr t_struct_edge, tint, tint, tint]
    PROP (def_wedgerep (w,(u,v)))
    PARAMS (ptr; w; u; v)
    GLOBALS ()
    SEP (data_at sh t_struct_edge rubbish ptr)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at sh t_struct_edge (w, (u, v)) ptr).

Definition init_empty_graph_spec :=
  DECLARE _init_empty_graph
  WITH gv: globals, sh: wshare
  PRE []
     PROP ()
     PARAMS ()
     GLOBALS (gv)
     SEP (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES))
  POST [ tptr t_wedgearray_graph ]
     EX gptr eptr: pointer_val,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val gptr))
     SEP ( (*explicit graph rep*)
          data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
          data_at sh (t_wedgearray_graph) (Vint (Int.repr 0), (Vint (Int.repr 0), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges MAX_EDGES) (pointer_val_val eptr)
         ).

Definition sort_edges_spec :=
 DECLARE _sort_edges
  WITH sh: share, a: val, al: list (reptype t_struct_edge)
  PRE [tptr t_struct_edge, tint]
    PROP (readable_share sh; writable_share sh;
      	 0 <= Zlength al <= Int.max_signed;
      	 Forall def_wedgerep al)
    PARAMS(a; Vint (Int.repr (Zlength al)))
    GLOBALS ()
    SEP(data_at sh (tarray t_struct_edge (Zlength al)) al a)
  POST [ tvoid ]
    EX bl: list (reptype t_struct_edge),
    PROP (Permutation al bl;
      	 forall i j, 0 <= i -> i <= j -> j < Zlength bl -> wedge_le (Znth i bl) (Znth j bl))
    LOCAL ()
    SEP(data_at sh (tarray t_struct_edge (Zlength bl)) bl a).

Definition kruskal_spec :=
  DECLARE _kruskal
  WITH gv: globals, sh: wshare, g: FiniteWEdgeListGraph, orig_gptr : pointer_val, orig_eptr : pointer_val,
       glist: list (LE*EType)
  PRE [tptr t_wedgearray_graph]
  PROP (sound_weighted_edge_graph g;
        forall v, 0 <= v < (numV g) <-> vvalid g v;
        numE g <= MAX_EDGES;
        0 < numV g <= Int.max_signed / 8;
        Permutation (graph_to_wedgelist g) glist
       )
   PARAMS ((pointer_val_val orig_gptr))
   GLOBALS (gv)
   SEP (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
        (**original graph*)
          data_at sh (t_wedgearray_graph) (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata glist ++ (Vundef_cwedges (MAX_EDGES - numE g))) (pointer_val_val orig_eptr)
        )
  POST [tptr t_wedgearray_graph]
   EX msf_gptr msf_eptr: pointer_val,
   EX msf: FiniteWEdgeListGraph,
   EX msflist: list (LE*EType),
   EX glist': list (LE*EType),
   PROP (
        Permutation (graph_to_wedgelist g) glist';
      	(*forall i j, 0 <= i -> i <= j -> j < Zlength glist' -> wedge_le (wedge_to_cdata (Znth i glist')) (wedge_to_cdata (Znth j glist'));*)
        sound_weighted_edge_graph msf;
        (numE msf) <= MAX_EDGES;
        Permutation msflist (graph_to_wedgelist msf);
        minimum_spanning_forest (lg_gg g) (lg_gg msf) Z.add 0 Z.le)
   LOCAL (temp ret_temp (pointer_val_val msf_gptr))
   SEP (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
        (*original graph*)
          data_at sh (t_wedgearray_graph) (Vint (Int.repr (numV g)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata glist' ++ (Vundef_cwedges (MAX_EDGES - numE g))) (pointer_val_val orig_eptr);
        (*mst*)
          data_at sh (t_wedgearray_graph) (Vint (Int.repr (numV msf)), (Vint (Int.repr (numE msf)), pointer_val_val msf_eptr)) (pointer_val_val msf_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata msflist ++ (Vundef_cwedges (MAX_EDGES - numE msf))) (pointer_val_val msf_eptr)
        ).