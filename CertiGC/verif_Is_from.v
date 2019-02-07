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

Lemma intmod_eq_ptrofsmod: Int.modulus = Ptrofs.modulus.
Proof. now unfold Archi.ptr64; apply Ptrofs.modulus_eq32. Qed.

Lemma lt_ptr_mod: forall n1 n2,
    n1 <= n2 <= Ptrofs.max_unsigned -> n1 <= n2 < Ptrofs.modulus.
Proof.
  intros.
  replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by rep_omega.
  now rewrite <- Z.lt_le_pred in *.
Qed.

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
  - intros. exists f, vres, m1'. destruct H0 as [? [? ?]]. 
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
    assert (Hf: 0 <= Ptrofs.unsigned i + n < Ptrofs.modulus) by  
        (unfold Ptrofs.unsigned, Ptrofs.intval; destruct i;
         split; [omega | auto]).
    assert (Ha: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta)) + n < Int.modulus). {
      rewrite intmod_eq_ptrofsmod.
      destruct H1 as [_ _ _ _ rep _].
      generalize (rep b0 b3 delta
                      (Ptrofs.add i (Ptrofs.repr n)) H22).
      intros [Hx Hy].
      { right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]].
        assert (Hm: 0 <= n - 1 < n) by omega.
        rewrite <- (H5 _ Hm).
        f_equal.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega. }
      clear -Hy Hf H0 Hx.
      apply lt_ptr_mod in Hy.
      destruct Hy as [Hy' Hy].
      unfold Ptrofs.add in *.
      repeat rewrite Ptrofs.unsigned_repr_eq in *.
      rewrite Z.add_mod_idemp_r, Z.mod_small in Hy, Hy' by easy.
      rewrite Z.add_mod_idemp_r by easy.
      rewrite Z.mod_small; [omega|].
      destruct i. unfold Ptrofs.unsigned in *; simpl in *. omega.
    }
    split3; [| |split3; [| |split3]]; trivial.
    + unfold Ptrofs.add. rewrite <- H4.
      destruct (Ptrofs.unsigned_range i) as [? _].
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Z.add_mod_idemp_r by easy.
      rewrite intmod_eq_ptrofsmod in Ha.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta
                   (Ptrofs.add i (Ptrofs.repr n)) H22) as [Hd' Hd]. {
        right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]].
        assert (0 <= n - 1 < n) by omega.
        rewrite <- (H5 _ H1). f_equal.
        unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy.
        omega.
      }
      unfold Ptrofs.add in Hd.
      repeat rewrite Ptrofs.unsigned_repr_eq in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small in Hd by easy.
      apply lt_ptr_mod in Hd.
      repeat rewrite Z.mod_small; [omega | trivial | omega].
    + split3; [easy | omega|]. intros.
      destruct H5 as [_ [_ H5]]. assert (Hs := H5).
      specialize (H5 i2 H3).
      rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H22 H1 H5).
      f_equal. unfold Ptrofs.add.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta i H22) as [_ Hd]. {
        left. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        assert (0 <= 0 < n) by omega.
        specialize (Hs 0 H1). rewrite <- Hs. f_equal. omega.
      } 
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r by easy.
      rewrite Z.mod_small by easy. omega.
    + rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H32 H1 H6).
      f_equal. unfold Ptrofs.add.
      repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta1 i1 H32) as [_ Hd]. {
        left; now apply Mem.perm_cur_max,
              Mem.valid_pointer_nonempty_perm.
      }
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
    + destruct H7.
      * destruct H3 as [? [? ?]].
        destruct H1 as [_ _ _ _ rep _].
        destruct (rep b0 b3 delta i H22) as [_ Hp]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          destruct H5 as [_ [_ H1]]; assert (H5: 0 <= 0 < n) by omega.
          specialize (H1 0 H5).
          now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H1 by omega.
        }
        destruct (rep b0 b3 delta i1 H22) as [_ Hq]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
            destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega.
          specialize (H1 0 H5); now rewrite H3.
        }
        destruct (rep b0 b3 delta i0 H22) as [_ Hr]. {
          destruct H5 as [_ [_ H5]].
          rewrite <- H4.
          assert (Hm: 0 <= n - 1 < n) by omega.
          right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          rewrite <- (H5 _ Hm); f_equal; omega.
        }
        subst b0.
        rewrite H22 in H32; inversion H32.
        left. split3; trivial.
        subst delta1. clear -H7 Hp Hq Hr.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr.  
        repeat rewrite Z.add_mod_idemp_r, Z.mod_small by easy.
        omega.
      * destruct H3. right. split; trivial.
        rename m2 into m. rename m1' into m'.
        destruct H1 as [[perm _ _] _ _ lap rep inv].
        destruct H3.
        -- destruct (EqDec_block b3 b7); [subst b3 | now left].
           right; split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           assert (Hs := H5).
           destruct H5 as [_ [_ H5]].
           assert (bound: 0 <= 0 < n) by omega.
           specialize (H5 _ bound).
           clear bound.
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H6.
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H5.
           replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H5 by omega.
           (* specialize (lap b0 b7 delta b1 b7 delta1 (Ptrofs.unsigned i) (Ptrofs.unsigned i1) H3 H22 H32 H5 H6). (**) *)
           specialize (lap _ _ _ _ _ _ _ _ H1 H22 H32 H5 H6). (**)
           destruct (rep _ _ delta1 i1 H32) as [_ Hp].
           1: left; easy.
           destruct (rep _ _ delta i H22) as [_ Hq].
           1: left; easy.
           destruct (rep _ _ delta i0 H22) as [_ Hr]. {
             destruct Hs as [_ [_ Hs]]. 
             rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             specialize (Hs _ Hm).
             replace (Ptrofs.unsigned i + (n - 1)) with (Ptrofs.unsigned i + n - 1) in Hs by omega.
             apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in Hs. now right.
           }
           replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by rep_omega.
           rewrite <- Z.lt_le_pred in *.
           repeat rewrite Z.mod_small by easy.
           destruct lap as [? | lap]; [contradiction|].
           clear rep Hp Hq Hr.
           replace (Ptrofs.unsigned i) with ((Ptrofs.unsigned i - delta) + delta) in H5 by omega.
           destruct Hs as [_ [_ Hs]].
           specialize (perm b0 b7 delta (Ptrofs.unsigned i - delta) Max Nonempty H22).
           specialize (inv _ (Ptrofs.unsigned i - delta) _ _ Max Nonempty H22).
           (* Hrm... kinda worked myself into a corner.
            * Feels circular and weird. 
            * Consider perm --> inv.
            * Plus, specializing Hs is hard 
            *   cuz I would want "-delta" for i0, 
            *   and good luck proving the bound for that.
            *)
           (* stuck.
            * too many seemingly unrelated variables
            * and no disjunction above the bar.
            *)
           admit.
        -- destruct H3. subst b0.
           right. rewrite H22 in H32; inversion H32.
           split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           destruct H1 as [_ _ _ _ rep _].
           subst delta1.           
           destruct (rep b1 b3 delta i H22) as [_ Hp]. {
             left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             destruct H5 as [_ [_ H1]]; assert (H5: 0 <= 0 < n) by omega.
             specialize (H1 0 H5).
             now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H1 by omega.
           }
           destruct (rep b1 b3 delta i1 H22) as [_ Hq]. {
             now left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
           }
           destruct (rep b1 b3 delta i0 H22) as [_ Hr]. {
             destruct H5 as [_ [_ H5]].
             rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             rewrite <- (H5 _ Hm); f_equal; omega.
           }
           clear - H8 Hp Hq Hr.
           apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr. 
           repeat rewrite Z.mod_small by easy.
           destruct H8; [left | right]; omega.
(** External calls must commute with memory injections,
  in the following sense.
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