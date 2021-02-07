Require Import VST.floyd.proofauto.
Require Import CertiGraph.binheap.binary_heap_Zmodel.
Require Export CertiGraph.binheap.binary_heap_pro.
Require Export CertiGraph.binheap.env_binary_heap_pro.

Definition exch_spec :=
  DECLARE _exch WITH j : Z, k : Z, arr: val, arr_contents: list heap_item, lookup : val, lookup_contents : list Z
  PRE [tuint, tuint, tptr t_item, tptr tuint]
    PROP (0 <= j < Zlength arr_contents; 0 <= k < Zlength arr_contents)
    PARAMS (Vint (Int.repr j); Vint (Int.repr k); arr; lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX lookup_contents' : list Z,
      PROP (lookup_oob_eq (Zexchange arr_contents j k) lookup_contents lookup_contents')
      LOCAL ()
      SEP (linked_heap_array (Zexchange arr_contents j k) arr lookup_contents' lookup).

Definition less_spec :=
  DECLARE _less WITH i : Z, j : Z, arr: val, arr_contents: list heap_item, arr' : val, lookup : list Z
  PRE [tuint, tuint, tptr t_item]
    PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
    PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup arr')
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Val.of_bool (cmp (Znth i arr_contents) (Znth j arr_contents))))
    SEP (linked_heap_array arr_contents arr lookup arr').

Definition swim_spec :=
  DECLARE _swim WITH k : Z, arr: val, arr_contents: list heap_item, lookup : val, lookup_contents : list Z
  PRE [tuint, tptr t_item, tptr tuint]
    PROP (0 <= k < Zlength arr_contents;
          weak_heap_ordered_bottom_up arr_contents k)
    PARAMS (Vint (Int.repr k); arr; lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX arr_contents' : list (Z * int * int), EX lookup_contents' : list Z,
      PROP (lookup_oob_eq arr_contents' lookup_contents lookup_contents'; 
            heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup_contents' lookup).

Definition sink_spec :=
  DECLARE _sink WITH k : Z, arr: val, arr_contents: list heap_item, first_available : Z, lookup : val, lookup_contents : list Z
  PRE [tuint, tptr t_item, tuint, tptr tuint]
    PROP (0 <= k <= Zlength arr_contents; 
          first_available = Zlength arr_contents;
          (k = Zlength arr_contents -> (2 * k) <= Int.max_unsigned);
          (k < Zlength arr_contents -> (2 * (first_available - 1) <= Int.max_unsigned)); (* i = fa - 1 -> (2 * i + 1) = 2 * fa - 1, must be representable *)
          weak_heap_ordered_top_down arr_contents k)
    PARAMS (Vint (Int.repr k); arr; Vint (Int.repr first_available); lookup)
    GLOBALS ()
    SEP (linked_heap_array arr_contents arr lookup_contents lookup)
  POST [tvoid]
    EX arr_contents' : list heap_item, EX lookup_contents' : list Z,
      PROP (lookup_oob_eq arr_contents' lookup_contents lookup_contents'; 
            heap_ordered arr_contents'; Permutation arr_contents arr_contents')
      LOCAL ()
      SEP (linked_heap_array arr_contents' arr lookup_contents' lookup).

Definition pq_size_spec := 
  DECLARE _pq_size WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_size h))))
    SEP (valid_pq pq h).

Definition capacity_spec := 
  DECLARE _capacity WITH pq : val, h : heap
  PRE [tptr t_pq]
    PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (heap_capacity h))))
    SEP (valid_pq pq h).

Definition pq_remove_min_nc_spec :=
  DECLARE _pq_remove_min_nc WITH pq : val, h : heap, i : val
  PRE [tptr t_pq, tptr t_item]
    PROP (heap_size h > 0)
    PARAMS (pq; i)
    GLOBALS ()
    SEP (valid_pq pq h; hitem_ i)
  POST [tvoid]
  EX h', EX iv : heap_item,
    PROP (heap_capacity h = heap_capacity h';
          Permutation (heap_items h) (iv :: heap_items h');
          Forall (cmp_rel iv) (heap_items h'))
    LOCAL ()
    SEP (valid_pq pq h'; hitem iv i).

Definition pq_insert_nc_spec :=
  DECLARE _pq_insert_nc WITH pq : val, h : heap, priority : Z, data : int
  PRE [tptr t_pq, tint, tint]
    PROP (heap_size h < heap_capacity h)
    PARAMS (pq; Vint (Int.repr priority); Vint data)
    GLOBALS ()
    SEP (valid_pq pq h)
  POST [tuint]
  EX h' : heap, EX key : Z,
    PROP (heap_capacity h = heap_capacity h';
          Permutation (((key, Int.repr priority, data): heap_item) :: heap_items h) (heap_items h'))
    LOCAL (temp ret_temp (Vint (Int.repr key)))
    SEP (valid_pq pq h').

Definition pq_make_spec := 
  DECLARE _pq_make WITH size : Z
  PRE [tuint]
  PROP (4 <= 12 * size <= Int.max_unsigned)
    PARAMS (Vint (Int.repr size))
    GLOBALS ()
    SEP ()
  POST [tptr t_pq]
    EX pq: val, EX h : heap,
    PROP (heap_size h = 0;
         heap_capacity h = size)
    LOCAL (temp ret_temp pq)
    SEP (valid_pq pq h). (* and the free_toks I get from mallocN *)

Definition pq_free_spec := 
  DECLARE _pq_free WITH pq : val, h : heap
  PRE [tptr t_pq]
  PROP ()
    PARAMS (pq)
    GLOBALS ()
    SEP (valid_pq pq h) (* and the free toks I get from pq_make*)
  POST [tvoid]
    PROP ()
    LOCAL ()
    SEP (emp). 

Definition pq_edit_priority_spec := 
  DECLARE _pq_edit_priority WITH pq : val, h : heap, key : Z, newpri : int
  PRE [tptr t_pq, tint, tint]
  PROP (In key (proj_keys h))
    PARAMS (pq; Vint (Int.repr (key)); Vint newpri)
    GLOBALS ()
    SEP (valid_pq pq h) (* and the free toks I get from pq_make*)
  POST [tvoid]
    EX h': heap,
    PROP (Permutation (heap_items h') (update_pri_by_key (heap_items h) key newpri);
         heap_capacity h' = heap_capacity h)
    LOCAL ()
    SEP (valid_pq pq h').

