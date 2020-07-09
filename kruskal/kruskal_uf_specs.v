(* UF's imports (already made minimal *)
Require Import RamifyCoq.sample_mark.env_unionfind_arr.
Require Export RamifyCoq.sample_mark.uf_arr_specs.

(* Kruskal's imports (already made minimal *)
Require Import RamifyCoq.graph.undirected_graph.
Require Import RamifyCoq.kruskal.WeightedEdgeListGraph.
Require Import RamifyCoq.kruskal.env_kruskal_edgelist.
Require Import RamifyCoq.kruskal.spatial_wedgearray_graph.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope Z_scope.

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
        minimum_spanning_forest msf g
        )
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

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [makeSet_spec; find_spec; union_spec; freeSet_spec;
      mallocK_spec; fill_edge_spec; init_empty_graph_spec; sort_edges_spec; kruskal_spec
  ]).
