Require Export CertiGraph.priq.priq_arr.
Require Export CertiGraph.priq.priq_arr_utils.
Require Export VST.floyd.proofauto.

(* Specs for Anshuman's simple array-based PQ *)

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Local Open Scope Z_scope.

(* 
 * These specs are parameterized by the ID of the _function.
   Con: Nonstandard 
   Neutral: I claim it is mathematically irrelevant
   Pro: Lets me feed in PQ's _function now, 
        and later feed in Dijk's _function
        while reusing the same actual spec, as one
        would want to.
*)

Definition push_spec push :=
  DECLARE push
  WITH pq: val, vertex : Z, weight : Z, priq_contents_val: list val
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE;
       weight_inrange_priq weight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr weight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) priq_contents_val pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                         priq_contents_val (Vint (Int.repr weight))) pq).
    
Definition pq_emp_spec pq_emp := 
  DECLARE pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents)
   PARAMS (pq)
   GLOBALS ()
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (isEmpty priq_contents))
   SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq).

Definition adjustWeight_spec adjustWeight :=
  DECLARE adjustWeight
  WITH pq: val, vertex : Z, newWeight : Z, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < SIZE;
       weight_inrange_priq newWeight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr newWeight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                  (map Vint (map Int.repr priq_contents)) (Vint (Int.repr newWeight))) pq).

Definition popMin_spec popMin :=
  DECLARE popMin
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (inrange_priq priq_contents;
        isEmpty priq_contents = Vzero)
   PARAMS (pq)
   GLOBALS ()
   SEP   (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   EX rt : Z,
   PROP (rt = priq_arr_utils.find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
   LOCAL (temp ret_temp  (Vint (Int.repr rt)))
   SEP   (data_at Tsh (tarray tint SIZE) (upd_Znth
                                            (priq_arr_utils.find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
                                            (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition Gprog : funspecs :=
  ltac:(with_library prog
                     [push_spec _push;
                     pq_emp_spec _pq_emp;
                     adjustWeight_spec _adjustWeight;
                     popMin_spec _popMin]).
