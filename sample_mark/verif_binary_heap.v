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
  rewrite Znth_map.
  entailer!. trivial.
  forward.
  rewrite Znth_map.
  entailer!. trivial.
  (* Why is this goal here? *)
  admit.
  trivial.
  forward.
  rewrite Znth_map.
  rewrite Znth_map.
  entailer!. trivial. trivial.
  forward; trivial.
  forward; trivial.
  rewrite Znth_map; auto.
  rewrite Znth_map; auto.
  entailer!.
(*
rewrite Zlength_upd_Znth in H3.
rewrite Zlength_map in H3.
*)
rewrite Forall_Znth in H4.
apply H4; clear H3 H4; auto.
rewrite Zlength_upd_Znth.
rewrite Zlength_map. trivial.
assert (Heq: i = j \/ i <> j) by lia. destruct Heq.
+ subst j. rewrite upd_Znth_same. simpl.
auto.

Search repinject.
simpl.

specialize (H4 j H0). si
apply H4.
Search Forall Znth.

rewrite upd_Znth_map in H4.
 rewrite upd_Znth_same in *.

generalize (upd_Znth_same j (map (fun p : Z * Z => (Vint (Int.repr (fst p)), Vint (Int.repr (snd p)))) arr_contents)).

Znth_upd_Znth_diff:
  forall (A : Type) (d : Inhabitant A) (i j : Z) (l : list A) (x : A), i <> j -> Znth i (upd_Znth j l x) = Znth i l
upd_Znth_same:
  forall (A : Type) (d : Inhabitant A) (i : Z) (l : list A) (u : A), 0 <= i < Zlength l -> Znth i (upd_Znth i l u) = u
Znth_upd_Znth_same:
  forall (A : Type) (d : Inhabitant A) (i j : Z) (l : list A) (x : A),
  0 <= i < Zlength l -> i = j -> Znth i (upd_Znth j l x) = x
upd_Znth_diff:
  forall (A : Type) (d : Inhabitant A) (i j : Z) (l : list A) (u : A),
  0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j -> Znth i (upd_Znth j l u) = Znth i l

rewrite <- upd_Znth_map.

upd_Znth i (map (fun p : Z * Z => (Vint (Int.repr (fst p)), Vint (Int.repr (snd p)))) arr_contents)

rewrite Znth_upd_Znth.
Search Zlength upd_Znth.
 
rewrite upd_Znth_map in H3. 
Search upd_Znth map.
  rewrite Znth_map.

  rewrite Znth_map.
  rewrite Znth_map.



ata_at Tsh (tarray tint SIZE)
               (upd_Znth vertex
                         priq_contents_val (Vint (Int.repr weight))) pq).


(* We must use the CompSpecs and Vprog that were
   centrally defined in dijksta's environment. 
   This lets us be consistent and call PQ functions in Dijkstra. 
 *)

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute. trivial. Qed.

Lemma body_push: semax_body Vprog Gprog f_push push_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP (isEmpty_Prop (sublist 0 i priq_contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; lia.
  - unfold SIZE; rep_lia.
  - entailer!. 
  - simpl.
    assert_PROP (Zlength priq_contents = SIZE). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)).
      * trivial.
      * apply Znth_In; lia.
      * rewrite <- H1 in H0.
        pose proof (Forall_Znth _ _ i H0 H).
        rewrite Int.signed_repr in H3.
        apply (Z.lt_stepr _ _ _ H3). compute; trivial.
        simpl in H7. rep_lia.
    + rewrite (sublist_split 0 i (i+1)); try lia.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      Opaque inf.
      rewrite sublist_one; try lia. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) (inf + 1)).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3.
      rewrite Int.add_signed in H3.
      Transparent inf.
      assert (Hx: inf + 1 < Int.max_signed) by 
          (compute; trivial). 
      rewrite Int.signed_repr in H3.
      2: rewrite <- H1 in H0; apply (Forall_Znth _ _ i H0) in H; simpl in H; rep_lia.
      rewrite Int.signed_repr in H3.
      2: { rewrite Int.signed_repr; [| rep_lia].
           rewrite Int.signed_repr; [| rep_lia].
           rep_lia.
      }
      do 2 rewrite Int.signed_repr in H3. lia.
      all: compute; split; inversion 1.
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: { symmetry; repeat rewrite Zlength_map in H2.
         unfold SIZE. simpl in H2. lia. }
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry. apply isEmpty_prop_val; trivial.
Qed.

Lemma body_adjustWeight: semax_body Vprog Gprog f_adjustWeight adjustWeight_spec.
Proof. start_function. forward. entailer!. Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = SIZE). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)) by
      (rewrite Zlength_map; rewrite H1; unfold SIZE; lia).
  assert (0 <= 0 < Zlength priq_contents) by
      (rewrite H1; unfold SIZE; lia).
  forward. forward.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
                        temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0)));
                        temp _pq pq)
                 SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_lia.
  - entailer!. simpl. rewrite find_index.
    trivial. lia. simpl. unfold not. lia.
  - forward.
    assert (0 <= i < Zlength priq_contents) by lia.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      pose proof (Forall_Znth _ _ x0 H6 H).
      simpl in H8. rep_lia.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      apply (Forall_sublist _ 0 i _) in H.
      apply (Forall_Znth _ _ _ H6) in H.
      simpl in H. rep_lia.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (Forall_Znth _ _ _ H5) in H; simpl in H; rep_lia. }
    forward_if.
    + forward. forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_r; [|lia].
      split; trivial. f_equal.
      rewrite find_index; trivial.
      apply min_not_in_prev; trivial.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite (sublist_one i (i+1) priq_contents) by lia.
      rewrite fold_min_another.
      rewrite Z.min_l; [|lia]. split; trivial.
  - forward.
    + entailer!. rewrite <- H1.
      apply find_range.
      rewrite sublist_same; [|lia..].
      apply min_in_list; [apply incl_refl | apply Znth_In; lia].
    + forward.
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 SIZE priq_contents)) 0).
      rewrite sublist_same by lia. entailer!.
      destruct priq_contents; simpl; auto.
Qed.
