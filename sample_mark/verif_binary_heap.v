Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.binary_heap_model.
Require Import RamifyCoq.sample_mark.binary_heap.
(* Require Import VST.floyd.sublist. *)

(* This may get bundled elsewhere at some point. *)
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.

Definition t_item := Tstruct _structItem noattr.

Definition harray (contents : list (Z * Z)) (ptr : val) : mpred :=
  data_at Tsh (tarray t_item (Zlength contents)) (map (fun p => (Vint (Int.repr (fst p)), Vint (Int.repr (snd p)))) contents) ptr.

Definition exch_spec :=
  DECLARE _exch
  WITH i : Z, j : Z, arr: val, arr_contents: list (Z * Z)
  PRE [tuint, tuint, tptr t_item]
  PROP (0 <= i < Zlength arr_contents; 0 <= j < Zlength arr_contents)
  PARAMS (Vint (Int.repr i); Vint (Int.repr j); arr)
  GLOBALS ()
  SEP (harray arr_contents arr)
  POST [tvoid]
  PROP ()
  LOCAL ()
  SEP (harray (exchange arr_contents (Z.to_nat i) (Z.to_nat j)) arr).

Definition Gprog : funspecs :=
         ltac:(with_library prog [ exch_spec ]).

Lemma body_exch: semax_body Vprog Gprog f_exch exch_spec.
Proof.
  start_function.
  unfold harray.
  forward.
  - rewrite Znth_map; trivial.
    entailer!.
  - forward.
    + rewrite Znth_map; trivial.
      entailer!. 
      (* Why is this goal here?
         Absolutely no idea *)
      admit.
    + Opaque Znth.
      forward.
      1: repeat rewrite Znth_map; trivial; entailer!.
      repeat rewrite Znth_map; trivial.
      forward. forward.
      * entailer!.
        clear H3. (* it's useless info *)
        (* rewrite Forall_Znth in H4. *)
        (* apply H4; clear H4. *)
        (* 1: rewrite Zlength_upd_Znth, Zlength_map; trivial. *)
        destruct (Z.eq_dec i j).
        -- subst j. rewrite upd_Znth_same.
           2: rewrite Zlength_map; auto.
           rewrite Znth_map; trivial.
        -- rewrite upd_Znth_diff.  
           2,3: rewrite Zlength_map; auto.
           2: lia.
           rewrite Znth_map; trivial.
           simpl. (* and we're back at the old goal *)
           admit.
      * forward. forward. forward.
Admitted.
        
(*        
        simpl.
        unfold harray.
entailer!.
rewrite Znth_map; auto.
replace (Zlength (exchange arr_contents (Z.to_nat i) (Z.to_nat j))) with (Zlength arr_contents).
2: admit.
repeat rewrite upd_Znth_map in *.
admit.
Admitted.

*)
