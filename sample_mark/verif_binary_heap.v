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

Lemma upd_Znth_overwrite:
  forall {A} (l : list A) i a b,
    0 <= i < Zlength l ->
    upd_Znth i (upd_Znth i l a) b = upd_Znth i l b.
Proof.
  intros.
  rewrite upd_Znth_unfold by now rewrite upd_Znth_Zlength.
  rewrite upd_Znth_Zlength; trivial.
  repeat rewrite upd_Znth_unfold by trivial.
  rewrite sublist0_app1.
  2: rewrite Zlength_sublist; lia.
  rewrite sublist_sublist00 by lia.
  f_equal. f_equal.
  rewrite app_assoc.
  rewrite sublist_app2.
  2: { rewrite Zlength_app, Zlength_sublist by lia.
       unfold Zlength; simpl; lia. }
  rewrite Zlength_app, Zlength_sublist by lia.
  unfold Zlength at 1; simpl.
  rewrite sublist_same; trivial; [lia|].
  unfold Zlength at 2; simpl.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

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
        repeat rewrite upd_Znth_overwrite by
            (repeat rewrite upd_Znth_Zlength; rewrite Zlength_map; trivial).
        repeat rewrite upd_Znth_same by
            (try rewrite upd_Znth_Zlength; rewrite Zlength_map; easy).
        entailer!.
        destruct (Z.eq_dec i j).
        -- subst i.
           repeat rewrite upd_Znth_same by
               (try rewrite upd_Znth_Zlength; rewrite Zlength_map; easy).
           rewrite upd_Znth_overwrite by
               (repeat rewrite upd_Znth_Zlength; rewrite Zlength_map; trivial).
           unfold harray.
           entailer!.
           (* does nothing: it can't 
              read into exchange *)
           unfold exchange.
           (* oh wow, perhaps it would be good to
              modify exchange to take Zs? *)
           admit.
        -- rewrite upd_Znth_diff; trivial.
           2,3: rewrite Zlength_map; trivial.
           2: lia.
           rewrite Znth_map; trivial.
           admit.
Admitted.
