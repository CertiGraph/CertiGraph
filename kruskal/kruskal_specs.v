(* UF's imports (already made minimal *)
Require Import CertiGraph.unionfind.env_unionfind_arr.
Require Export CertiGraph.unionfind.uf_arr_specs.

(* Kruskal's imports (already made minimal *)
Require Import CertiGraph.kruskal.WeightedEdgeListGraph.
Require Export CertiGraph.kruskal.env_kruskal_edgelist.
Require Import CertiGraph.kruskal.spatial_wedgearray_graph.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.floyd_ext.share.
Require Import VST.floyd.library.

Local Open Scope Z_scope.

(* KRUSKAL SPECS *)

(*Taken from VST's queue*)
Parameter malloc_token': share -> Z -> val -> mpred.

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
  WITH gv: globals, sh: share
  PRE []
     PROP (writable_share sh)
     PARAMS ()
     GLOBALS (gv)
     SEP (mem_mgr gv; data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES))
  POST [ tptr t_wedgearray_graph ]
     EX gptr eptr: pointer_val,
     PROP ()
     LOCAL (temp ret_temp (pointer_val_val gptr))
     SEP ( (*explicit graph rep*)
          mem_mgr gv;
          malloc_token' sh (MAX_EDGES * sizeof t_struct_edge) (pointer_val_val eptr);
          malloc_token' sh (sizeof t_wedgearray_graph) (pointer_val_val gptr);
          data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
          data_at sh (t_wedgearray_graph) (Vint (Int.repr 0), (Vint (Int.repr 0), pointer_val_val eptr)) (pointer_val_val gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES) (Vundef_cwedges MAX_EDGES) (pointer_val_val eptr)
         ).

Definition swap_edges_spec :=
 DECLARE _swap_edges
  WITH sh: share, a : reptype t_struct_edge, b: reptype t_struct_edge, a_ptr: val, b_ptr: val
  PRE [tptr t_struct_edge, tptr t_struct_edge]
    PROP (readable_share sh; writable_share sh; def_wedgerep a; def_wedgerep b)
    PARAMS (a_ptr; b_ptr)
    GLOBALS ()
    SEP (data_at sh t_struct_edge a a_ptr; data_at sh t_struct_edge b b_ptr)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at sh t_struct_edge b a_ptr; data_at sh t_struct_edge a b_ptr).

Definition yucky_find_min_spec :=
 DECLARE _yucky_find_min
  WITH sh: share, a: val, al: list (reptype t_struct_edge), lo :Z, hi: Z
  PRE [tptr t_struct_edge, tint, tint]
    PROP (readable_share sh; writable_share sh;
      	  Forall def_wedgerep al;
          0 <= lo < hi;
          hi <= Zlength al <= Int.max_signed
         )
    PARAMS(a; Vint (Int.repr lo); Vint (Int.repr hi))
    GLOBALS ()
    SEP(data_at sh (tarray t_struct_edge (Zlength al)) al a)
  POST [ tint ]
    EX min: Z,
    PROP (lo <= min < hi;
          forall i, lo <= i < hi -> wedge_le (Znth min al) (Znth i al)
         )
    LOCAL (temp ret_temp (Vint (Int.repr min)))
    SEP(data_at sh (tarray t_struct_edge (Zlength al)) al a).

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

Section kruskal_spec.

Context {size: Z}.

Definition kruskal_spec :=
  DECLARE _kruskal
  WITH gv: globals, sh: wshare, g: (@EdgeListGG size), orig_gptr : pointer_val, orig_eptr : pointer_val,
       glist: list (LE*EType)
  PRE [tptr t_wedgearray_graph]
  PROP (numE g <= MAX_EDGES;
        0 < size <= Int.max_signed / 8;
        Permutation (graph_to_wedgelist g) glist
       )
   PARAMS ((pointer_val_val orig_gptr))
   GLOBALS (gv)
   SEP (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
        (**original graph*)
          data_at sh (t_wedgearray_graph) (Vint (Int.repr (size)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata glist ++ (Vundef_cwedges (MAX_EDGES - numE g))) (pointer_val_val orig_eptr)
        )
  POST [tptr t_wedgearray_graph]
   EX msf_gptr msf_eptr: pointer_val,
   EX msf: (@EdgeListGG size),
   EX msflist: list (LE*EType),
   EX glist': list (LE*EType),
   PROP (
        Permutation (graph_to_wedgelist g) glist';
      	(*forall i j, 0 <= i -> i <= j -> j < Zlength glist' -> wedge_le (wedge_to_cdata (Znth i glist')) (wedge_to_cdata (Znth j glist'));*)
        (numE msf) <= MAX_EDGES;
        Permutation msflist (graph_to_wedgelist msf);
        minimum_spanning_forest msf g
        )
   LOCAL (temp ret_temp (pointer_val_val msf_gptr))
   SEP (data_at sh tint (Vint (Int.repr MAX_EDGES)) (gv _MAX_EDGES);
        (*original graph*)
          data_at sh (t_wedgearray_graph) (Vint (Int.repr (size)), (Vint (Int.repr (numE g)), pointer_val_val orig_eptr)) (pointer_val_val orig_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata glist' ++ (Vundef_cwedges (MAX_EDGES - numE g))) (pointer_val_val orig_eptr);
        (*msf*)
          malloc_token' sh (MAX_EDGES * sizeof t_struct_edge) (pointer_val_val msf_eptr);
          malloc_token' sh (sizeof t_wedgearray_graph) (pointer_val_val msf_gptr);
          data_at sh (t_wedgearray_graph) (Vint (Int.repr size), (Vint (Int.repr (numE msf)), pointer_val_val msf_eptr)) (pointer_val_val msf_gptr);
          data_at sh (tarray t_struct_edge MAX_EDGES)
            (map wedge_to_cdata msflist ++ (Vundef_cwedges (MAX_EDGES - numE msf))) (pointer_val_val msf_eptr)
        ).

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog : funspecs :=
  ltac:(with_library prog
      [makeSet_spec; find_spec; union_spec; freeSet_spec;
      mallocK_spec; fill_edge_spec; swap_edges_spec; init_empty_graph_spec; yucky_find_min_spec; sort_edges_spec; kruskal_spec
  ]).

End kruskal_spec.