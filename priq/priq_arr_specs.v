Require Export CertiGraph.priq.priq_arr.
Require Export CertiGraph.priq.priq_arr_utils.
Require Export VST.floyd.proofauto.

(* Specs for Anshuman's simple array-based PQ *)

Section PriqSpec.

Context {CompSpecs: compspecs}.
Context {size: Z}.
Context {inf: Z}.
Instance Z_EqDec : EquivDec.EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.


Definition push_spec :=
  DECLARE _push
  WITH pq: val, vertex : Z, weight : Z, priq_contents_val: list val
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < size;
       @weight_inrange_priq inf weight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr weight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint size) priq_contents_val pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint size)
               (upd_Znth vertex
                         priq_contents_val (Vint (Int.repr weight))) pq).
    
Definition pq_emp_spec := 
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (@inrange_priq inf priq_contents)
   PARAMS (pq)
   GLOBALS ()
   SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (@isEmpty inf priq_contents))
   SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq).

Definition adjustWeight_spec :=
  DECLARE _adjustWeight
  WITH pq: val, vertex : Z, newWeight : Z, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < size;
       @weight_inrange_priq inf newWeight)
  PARAMS (Vint (Int.repr vertex);
          Vint (Int.repr newWeight);
          pq)
  GLOBALS ()
  SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (data_at Tsh (tarray tint size)
               (upd_Znth vertex
                  (map Vint (map Int.repr priq_contents)) (Vint (Int.repr newWeight))) pq).

Definition popMin_spec :=
  DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [tptr tint]
   PROP (@inrange_priq inf priq_contents;
        @isEmpty inf priq_contents = Vzero)
   PARAMS (pq)
   GLOBALS ()
   SEP   (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   EX rt : Z,
   PROP (rt = priq_arr_utils.find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
   LOCAL (temp ret_temp  (Vint (Int.repr rt)))
   SEP   (data_at Tsh (tarray tint size) (upd_Znth
                                            (priq_arr_utils.find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
                                            (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition Gprog: funspecs :=
  ltac:(with_library prog
                     [push_spec;
                     pq_emp_spec;
                     adjustWeight_spec;
                     popMin_spec]).

End PriqSpec.
