Require Export compcert.common.Events.
Require Export RamifyCoq.CertiGC.gc_spec.

Definition valid_block (m : mem) (b : block) (o : ptrofs) (n : Z) : Prop :=
  0 < n /\
  Ptrofs.unsigned o + n <= Int.modulus /\
  forall i : Z, 0 <= i < n ->
                common.Memory.Mem.valid_pointer m b (Ptrofs.unsigned o + i) = true.

Definition Is_from_sem : extcall_sem :=
  fun _ args m1 trc ret m2 =>
    m1 = m2 /\ trc = nil /\ 
    match args with
    | (Vptr b1 o1) :: (Vptr b2 o2) :: (Vptr b3 o3) :: nil =>
      exists n : Z, 0 < n /\ Ptrofs.unsigned o1 + n < Int.modulus /\
                    (b1 = b2) /\ (Ptrofs.unsigned o1 + n = Ptrofs.unsigned o2) /\
                    valid_block m1 b1 o1 n /\
                    common.Memory.Mem.valid_pointer m1 b3 (Ptrofs.unsigned o3) = true /\
                    ((b1 = b3 /\ (Ptrofs.unsigned o1 <=
                                  Ptrofs.unsigned o3 <
                                  Ptrofs.unsigned o2)
                      /\ ret = Vone) \/
                     (((b1 <> b3) \/
                       (b1 = b3 /\
                        (Ptrofs.unsigned o3 < Ptrofs.unsigned o1 \/
                         Ptrofs.unsigned o3 >= Ptrofs.unsigned o2)))
                      /\ ret = Vzero))
    | _ => False
    end.

Definition Is_from_sig : signature :=
  mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default.

Lemma Is_from_extcall: extcall_properties Is_from_sem Is_from_sig.
Proof.
  constructor.
  - intros. destruct H as [_ [_ ?]].
    do 4 (destruct vargs; try destruct v; try contradiction).
    destruct H as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    destruct H as [[_ [_ ?]] | [_ ?]]; subst; apply I.
  - intros. apply H0.
  - intros. destruct H as [? _]. subst m1. apply H0.
  - intros. destruct H as [? _]. subst m1. apply H1.
  - intros. destruct H as [? _]. subst m1.
    apply Mem.unchanged_on_refl.
  - intros. exists vres, m1'.
    destruct H as [? [? ?]]. subst m2 t.
    split. 2: { split. apply Val.lessdef_refl. split. trivial. apply Mem.unchanged_on_refl. }
    split. trivial. split. trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).    
    inversion H1. inversion H4. inversion H6. inversion H11.
    inversion H13. inversion H18. inversion H20. subst. clear H4 H11 H18 H20 H13 H6 H1.
    destruct H3 as [n [? [? [? [? ?]]]]].
    exists n. repeat (split; [assumption|]). clear H H1 H2 H3. 
    destruct H4 as [? [? ?]].
    split. {
      clear -H H0.
      destruct H as [? [? ?]]. do 2 (split; trivial).
      intros i0 Hx. specialize (H2 i0 Hx).
      eapply Mem.valid_pointer_extends; eauto. }
    split. eapply Mem.valid_pointer_extends; eauto.
    tauto.
  - intros. exists f, vres, m1'. destruct H0 as [? [? ?]]. (* subst m2 t. *)
    split.
    2: {
      split.
      - do 4 (destruct vargs; try destruct v; try contradiction). inversion H2. inversion H7. inversion H9.
      inversion H17. inversion H19.
      inversion H27. inversion H29.
      destruct H4 as [n [? [? [? [? [? [? ?]]]]]]]. 
      destruct vres; auto.  
      now destruct H41.
      - repeat (split; [now subst|]).
        apply mem_lemmas.inject_separated_same_meminj.
    }
    split3; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).
    inversion H2; inversion H7; inversion H9;
      inversion H17; inversion H19; inversion H27;
        inversion H29; subst.
    clear H2 H7 H9 H17 H19 H27 H29.
    destruct H4 as [n [? [? [? [? [? [? ?]]]]]]].
    subst. exists n. rewrite H22 in H12; inversion H12. subst.
    clear H12.
    split3; [| |split3; [| |split3]]; trivial.
    + destruct H1 as [? ? ? ? ? ?].
      specialize (mi_representable b0 b3 delta (* (Ptrofs.add i (Ptrofs.repr n)) *) i H22). 
      destruct mi_representable as [Hx Hy]. 
      1: left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
        destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega;
        specialize (H1 0 H3);
        now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H1 by omega.
      replace Int.modulus with Ptrofs.modulus by now unfold Archi.ptr64; apply Ptrofs.modulus_eq32.
      destruct Hy as [_ Hy].
      replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in Hy by rep_omega.
      rewrite <- Z.lt_le_pred in Hy.
      unfold Ptrofs.add.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      admit. (* IDK if this is true. *)
    + unfold Ptrofs.add; rewrite <- H4, Z.add_shuffle0.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      (* hmmm. *) 
      (* do we know that i+delta is less than modulus? *)
      (* destruct H5 as [? [? ?]]. *)
      (* specialize (H8 delta). *)
      (*
      assert (n + Ptrofs.unsigned (Ptrofs.repr delta) =
              Ptrofs.unsigned (Ptrofs.repr delta) + n) by omega.
      *)      
      admit.
    + destruct H1 as [? ? ? ? ? ?].
      unfold valid_block in *.
      destruct H5 as [? [? ?]].
      split3; trivial.
      * admit.
      * intros. admit.
    + admit. (* very similar, grr *)
    +
      destruct H7. destruct H3 as [? [? ?]].
      destruct H1 as [? ? ? ? ? ?].
      assert (Hz := mi_representable).
      specialize (Hz b0 b3 delta i H22).
      destruct Hz as [_ Hy1].
      1: left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
        destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega.
          specialize (H1 0 H5).
          now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H1 by omega.
      assert (Hz := mi_representable).
      specialize (Hz b0 b3 delta i1 H22).
      destruct Hz as [_ Hy2].
      1: left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
        destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega;
          specialize (H1 0 H5). now rewrite H3.
      assert (Hz := mi_representable).
      specialize (Hz b0 b3 delta i0 H22).
      destruct Hz as [_ Hy3].
      1: left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
        destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega;
          specialize (H1 0 H5). now rewrite H3.


      * destruct H1 as [? [? ?]].
        subst b0. rewrite H22 in H32; inversion H32.
        left. split3; trivial. subst delta1.
        clear -H7 Hy.
        unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq. admit.
      * destruct H3. destruct H3.
        -- right. split; trivial.
           pose proof block_eq_dec b3 b7. destruct H8; [|left; trivial].
           right. split; trivial.
           admit. (* easy, just treat as Zs *)
        -- destruct H3. subst b0. rewrite H22 in H32; inversion H32.
           right. split; trivial. right; split; trivial.
           admit. (* again, just treat as Zs *)
  
  (* unsigned_repr_range: *)
  (*   forall i : Z, 0 <= i -> 0 <= Ptrofs.unsigned (Ptrofs.repr i) <= i *)

(* Mem.valid_pointer_nonempty_perm: *)
(*   forall (m : mem) (b : block) (ofs : Z), *)
(*     Mem.valid_pointer m b ofs = true <-> Mem.perm m b ofs Cur Nonempty *)
                                                  
(* Mem.perm_cur_max: *)
(*   forall (m : mem) (b : block) (ofs : Z) (p : permission), *)
(*   Mem.perm m b ofs Cur p -> Mem.perm m b ofs Max p *)

      

(*      destruct H7.
      * destruct H7 as [? [? ?]].
        subst. rewrite H32 in H12; inversion H12.
        rewrite H32 in H22; inversion H22. subst.
        clear H22 H12.
        split. destruct H1. pose proof (mi_representable _ _ _ i H32).
        destruct H1.
        (* apply (mi_representable H32). *)
        admit.
        split; trivial.
        split. admit.
        split. clear -H1 H5. destruct H5 as [? [? ?]].
        split; trivial. split. 
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        destruct H1.
        repeat (split; try easy).
      split; trivial.
      (* Mem.address_inject. *)
      (* Mem.valid_pointer_inject_no_overflow: *)
      split; [admit|].
      split; [rewrite H22 in H12; now inversion H12|].
      split; [rewrite H22 in H12; inversion H12; subst;
              unfold Ptrofs.add; rewrite <- H9; admit|].
      split. 
      intuition.
      destruct H27.
      * destruct H0 as [? [? ?]]. subst.
        rewrite H12 in H22. inversion H22.
        rewrite H12 in H32; inversion H32.
        subst.
        intuition; try easy.
        5: { left. split; trivial; split; trivial.
             unfold Ptrofs.add. split.
             - repeat rewrite Ptrofs.unsigned_repr_eq.
               admit.
             - admit. }
        admit. admit. admit. admit.
      * destruct H0. destruct H0.
        -- admit.
        -- destruct H0. subst.
           rewrite H12 in H22. inversion H22.
           rewrite H12 in H32; inversion H32.
           subst.
           admit.
           (* intuition; try easy. *)
           (* 10 subgoals, none easy *) *)
      (*
(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    symbols_inject f ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem ge2 vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';
       *)
  - intros. destruct H as [_ [? _]]. subst t. simpl. omega.
  - intros. generalize H. destruct H as [_ [? _]]. subst t1. inversion H0. subst t2. clear H0. intro H.
      exists vres1, m1. apply H.
  - intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
      subst m1 m2 t1 t2. split. constructor. intros _.
      split; trivial.
      do 4 (destruct vargs; try destruct v; try contradiction).
      destruct H2 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
      destruct H4 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
      intuition; congruence.
Admitted.