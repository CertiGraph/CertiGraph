Require Import CertiGraph.prim.prim_env.
Require Export CertiGraph.priq.priq_arr_specs.
Require Import CertiGraph.graph.MathUAdjMatGraph.
Require Import CertiGraph.graph.SpaceUAdjMatGraph1.
Require Export CertiGraph.prim.prim1.

Local Open Scope Z_scope.

Section PrimSpec.

Context {size : Z}.
Context {inf : Z}.
Context {Z_EqDec : EquivDec.EqDec Z eq}.
  
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition G := @UAdjMatGG size inf.
Identity Coercion UAdjMatGG_G: G >-> UAdjMatGG.

Definition getCell_spec :=
  DECLARE _getCell
  WITH g: G,
       graph_ptr: pointer_val,
       addresses: list val,
       u: V,
       i : V
  PRE [tptr (tptr tint), tint, tint]
    PROP (0 <= i < size;
          0 <= u < size)
    PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
    GLOBALS ()
    SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val graph_ptr) addresses)
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr (Znth i (Znth u (@graph_to_symm_mat size g))))) 
    SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val graph_ptr) addresses).    

Definition initialise_list_spec :=
  DECLARE _initialise_list
  WITH arr : val, old_list: list val, a: Z
  PRE [tptr tint, tint, tint]
     PROP ( writable_share Tsh;
            repable_signed a;
            0 < size <= Int.max_signed
          )
     PARAMS ( arr; Vint (Int.repr size); Vint (Int.repr a))
     GLOBALS ()
     SEP (data_at Tsh (tarray tint size) (old_list) (arr))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at Tsh (tarray tint size) (repeat (Vint (Int.repr a)) (Z.to_nat size)) arr
         ).

Definition initialise_matrix_spec :=
  DECLARE _initialise_matrix
  WITH arr : val, old_contents: list (list Z), a: Z, addresses : list val
  PRE [tptr (tarray tint size), tint]
     PROP ( writable_share Tsh;
            Zlength old_contents = size;
            forall row, In row old_contents -> Zlength row = size;
            repable_signed a;
            0 < size <= Int.max_signed; (*this is not enough for malloc, requires*)
            size * (4 * size) <= Ptrofs.max_signed (*you can alloc the entire matrix. Can derive above from here*)
          )
     PARAMS ( arr ; Vint (Int.repr a) )
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh old_contents arr addresses)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (repeat (repeat a (Z.to_nat size)) (Z.to_nat size) ) arr addresses).

Definition prim_spec :=
  DECLARE _prim
  WITH g: G, garbage: list V, gptr : pointer_val, r: Z, parent_ptr : pointer_val, addresses : list val
  PRE [tptr (tptr tint), tint, tint, tint, tptr tint]
     PROP ( writable_share Tsh;
            vvalid g r;
          size * (4 * size) <= Ptrofs.max_signed;
          inf < Int.max_signed
          )
     PARAMS ( pointer_val_val gptr; (Vint (Int.repr size)); (Vint (Int.repr inf)); (Vint (Int.repr r)); pointer_val_val parent_ptr)
     GLOBALS ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr) addresses; 
          data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) garbage) (pointer_val_val parent_ptr)
         )
  POST [ tvoid ]
     EX mst: G,
     EX fmst: FiniteGraph mst,
     EX parents: list V,
     PROP ( (*connected_graph mst;*)
            @minimum_spanning_forest size inf mst g;
            Permutation (EList mst) (map (fun v => eformat (v, Znth v parents))
              (filter (fun v => Znth v parents <? size) (nat_inc_list (Z.to_nat size))))
          )
     RETURN ()
     SEP (@SpaceAdjMatGraph' size CompSpecs Tsh (@graph_to_symm_mat size g) (pointer_val_val gptr) addresses;
          data_at Tsh (tarray tint size) (map (fun x => Vint (Int.repr x)) parents) (pointer_val_val parent_ptr)
         ).

Definition mallocN_spec {CS: compspecs} :=
  DECLARE _mallocN
  WITH n: Z
  PRE [tint]
  PROP (4 <= n <= Int.max_unsigned)
  PARAMS (Vint (Int.repr n))
  GLOBALS ()
  SEP ()
  POST [ tptr tvoid ]
  EX v: pointer_val,
  PROP (malloc_compatible n (pointer_val_val v))
  LOCAL (temp ret_temp (pointer_val_val v))
  SEP (data_at_ Tsh (tarray tint (n / sizeof tint)) (pointer_val_val v) *
       free_tok (pointer_val_val v) n).

Definition freeN_spec {CS: compspecs} :=
  DECLARE _freeN
  WITH sh: share, p: pointer_val, n: Z, contents: list Z
    PRE [tptr tvoid]
    PROP ()
    PARAMS (pointer_val_val p)
    GLOBALS ()
    SEP (data_at sh (tarray tint n)
                 (map Vint (map Int.repr contents))
                 (pointer_val_val p) *
        free_tok (pointer_val_val p) (sizeof tint * n))
  POST [tvoid]
    PROP () LOCAL () SEP (emp).


Definition Gprog: funspecs :=
  ltac:(with_library prog
                     [(@push_spec size inf _);
                     (@pq_emp_spec size inf _);
                     (@popMin_spec size inf Z_EqDec _);
                     (@adjustWeight_spec size inf _);
                     (@init_spec size _);
                     freePQ_spec;
                     mallocN_spec;
                     freeN_spec;
                     getCell_spec;
                     initialise_list_spec;
                     initialise_matrix_spec;
                     prim_spec
       ]).

End PrimSpec.
