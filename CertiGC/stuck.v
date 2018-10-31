Require Import RamifyCoq.CertiGC.gc_spec.
Require Export RamifyCoq.CertiGC.gc.

Lemma body1:
  semax_body Vprog Gprog f_int_or_ptr_to_int int_or_ptr_to_int_spec.
Proof.
  start_function.
  unfold is_int in H.
  destruct x eqn:?; try contradiction.
  unfold semax.
Abort.

Lemma body2:
  semax_body Vprog Gprog f_int_or_ptr_to_ptr int_or_ptr_to_ptr_spec.
Proof.
  start_function.
  destruct x eqn:?; try contradiction.
Abort.

Lemma body3:
  semax_body Vprog Gprog f_int_to_int_or_ptr int_to_int_or_ptr_spec.
Proof.
  start_function.
  red in H.
  destruct x; try contradiction.
Abort.

Lemma body4:
  semax_body Vprog Gprog f_ptr_to_int_or_ptr ptr_to_int_or_ptr_spec.
Proof.
  start_function.
  unfold semax.
  Transparent SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Def.semax.
  (* unfold SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Def.semax. *)
Abort.

Lemma body5:
  semax_body Vprog Gprog f_Is_block Is_block_spec.
Proof.
  start_function.
  unfold semax.
Abort.

Lemma int_or_ptr_to_int_is_stuck: forall ge e le m v id,
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (talignas 2%N (tptr tvoid))) tint)
                     v -> False.
Proof.
  intros. inversion H; subst. simpl in H4.
  - inversion H2; subst.   
Abort.

Lemma int_or_ptr_to_ptr_is_stuck: forall ge e le m v id,
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (talignas 2%N (tptr tvoid))) (tptr tvoid))
                     v -> False.
Proof.
  intros. inversion H; subst.
  - inversion H2; subst.
    + simpl in H4.
Abort.

Lemma int_to_int_or_ptr_is_stuck: forall ge e le m v id,
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id tint) (talignas 2%N (tptr tvoid)))
                     v -> False.
Proof.
  intros. inversion H; subst.
  - inversion H2; subst.
    + simpl in H4.
Abort.

Lemma ptr_to_int_or_ptr_is_stuck: forall ge e le m v id,
    Clight.eval_expr ge e le m
                     (Ecast (Etempvar id (tptr tvoid)) (talignas 2%N (tptr tvoid)))
                     v -> False.
Proof.
  intros. inversion H; subst.
  - inversion H2; subst.
    + simpl in H4.
Abort.

Lemma test_int_or_ptr_is_stuck_on_ptr: forall ge e le m v id b o,
    le ! id = Some (Vptr b o) ->
    Clight.eval_expr ge e le m
                     (Ecast
                        (Ebinop Oand
                                (Ecast (Etempvar id (talignas 2%N (tptr tvoid))) tint) (*why 2 and not 4?*)
                                (Econst_int (Int.repr 1) tint) tint) tint)
                     v -> False.  
Proof.
  intros. inversion H0; subst. 2: inversion H1.
  simpl in H5.
  destruct v1; inversion H5; clear H5; subst.
  + inversion H3; subst. 2: inversion H1.
    inversion H7; subst. 2: inversion H1.
    inversion H4; subst. 2: inversion H1.
    rewrite H in H10. inversion H10; subst; clear H H10.
    inversion H6; subst; clear H6.
    destruct v2; inversion H9.
  + clear H.
    inversion H3; subst. 2: inversion H.
    inversion H6; subst. 2: inversion H.
    inversion H2; subst. 2: inversion H.
    destruct v1; destruct v2; inversion H8.
Qed.

(*
Lemma is_from_is_stuck_for_ptr: ...
    le ! id1 = Some (Vptr b1 o1) ->
    le ! id2 = Some (Vptr b2 o2) ->
    b1 <> b1 ->
    blah ->
    False
*)      
  
  
  
