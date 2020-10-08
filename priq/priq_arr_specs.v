Require Export VST.floyd.proofauto.
Require Export CertiGraph.lib.find_lemmas.
Require Export CertiGraph.priq.is_empty_lemmas.
Require Export CertiGraph.priq.priq_arr.

(* Specs for Anshuman's simple array-based PQ *)
Section PQSpec.

Context {size : Z}.
Context {inf : Z}.
Parameter free_tok : val -> Z -> mpred.
Context {Z_EqDec : EquivDec.EqDec Z eq}. 

Definition weight_inrange_priq item :=
  Int.min_signed <= item <= inf.

Definition inrange_priq (priq : list Z) :=
  Forall (fun x => Int.min_signed <= x <= inf + 1) priq.

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

Definition freePQ_spec {CS: compspecs} :=
  DECLARE _freePQ
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

Definition init_spec {CS: compspecs} :=
  DECLARE _init
  WITH _: unit (* how to take nothing? *)
  PRE [tint]
  PROP (Int.min_signed <= size * 4 <= Int.max_signed;
       0 < size)
  PARAMS (Vint (Int.repr size))
  GLOBALS ()
  SEP ()
  POST [tptr tint]
  EX pq: pointer_val,
  PROP ()
  LOCAL (temp ret_temp (pointer_val_val pq))
  SEP (data_at_ Tsh (tarray tint size) (pointer_val_val pq) *
      free_tok (pointer_val_val pq) (sizeof tint * size)).

Definition push_spec {CS: compspecs} :=
  DECLARE _push
  WITH pq: val, vertex : Z, weight : Z, priq_contents_val: list val
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < size;
       (@weight_inrange_priq weight))
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
    
Definition pq_emp_spec {CS: compspecs} := 
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (@inrange_priq priq_contents;
       0 <= size <= Int.max_signed;
       0 <= inf;
       Int.min_signed < inf + 1 <= Int.max_signed)
   PARAMS (Vint (Int.repr size);
           Vint (Int.repr inf);
           pq)
   GLOBALS ()
   SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (@isEmpty inf priq_contents))
   SEP (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq).

Definition adjustWeight_spec {CS: compspecs} :=
  DECLARE _adjustWeight
  WITH pq: val, vertex : Z, newWeight : Z, priq_contents: list Z
  PRE [tint, tint, tptr tint]
  PROP (0 <= vertex < size;
       @weight_inrange_priq newWeight)
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

Definition popMin_spec {CS: compspecs} :=
  DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [tint, tint, tptr tint]
   PROP (@inrange_priq priq_contents;
        @isEmpty inf priq_contents = Vzero;
        0 < size <= Int.max_signed;
        0 <= inf;
        Int.min_signed < inf + 1 <= Int.max_signed)
   PARAMS (Vint (Int.repr size);
           Vint (Int.repr inf);
           pq)
   GLOBALS ()
   SEP   (data_at Tsh (tarray tint size) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
   EX rt : Z,
   PROP (rt = find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
   LOCAL (temp ret_temp  (Vint (Int.repr rt)))
   SEP   (data_at Tsh (tarray tint size) (upd_Znth
                                            (find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
                                            (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition Gprog {CS: compspecs}: funspecs :=
  ltac:(with_library prog
                     [mallocN_spec;
                     freePQ_spec;
                     init_spec;
                     push_spec;
                     pq_emp_spec;
                     adjustWeight_spec;
                     popMin_spec]).

End PQSpec.
