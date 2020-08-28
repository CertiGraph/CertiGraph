Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
(*Load "./byteint.v".*) (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)

Import VST.veric.base.
Import VST.msl.predicates_hered.
Import VST.veric.res_predicates.
Import VST.msl.predicates_sl.

Lemma Byte_modulus_value:
  Byte.modulus = 256.
Proof. compute; trivial. Qed.

Corollary Byte_unsigned_range:
  forall b: byte, 0 <= Byte.unsigned b < 256.
Proof.  
  rewrite <- Byte_modulus_value; apply Byte.unsigned_range.
Qed.

Corollary Byte_unsigned_range2:
  forall b: byte, 0 <= Byte.unsigned b <= 255.
Proof.
  intros. pose proof (Byte_unsigned_range b). lia.
Qed.

Lemma Int_modulus_value:
  Int.modulus = 4294967296.
Proof. compute; trivial. Qed.

Corollary Int_unsigned_range:
  forall i: int, 0 <= Int.unsigned i < 4294967296.
Proof.
  rewrite <- Int_modulus_value; apply Int.unsigned_range.
Qed.

Lemma Int_max_unsigned_value:
  Int.max_unsigned = 4294967295.
Proof. compute; trivial. Qed.

Lemma Ptrofs_max_unsigned_value:
  Ptrofs.max_unsigned = 4294967295.
Proof. compute; trivial. Qed.

Lemma vint_to_vbyte:
  forall a b: byte,
    Vint (Int.repr (Byte.unsigned a)) = Vubyte b <->
    Byte.unsigned a = Byte.unsigned b.
Proof.
  intros; split; intros.
  - inversion H.
    repeat rewrite Int.Z_mod_modulus_eq in H1.
    rewrite Zmod_small in H1.
    + rewrite Zmod_small in H1; [lia|].
      pose proof (Byte_unsigned_range b);
        rewrite Int_modulus_value; lia.
    + pose proof (Byte_unsigned_range a).
      rewrite Int_modulus_value; lia.
  - rewrite H. reflexivity.
Qed.

Lemma vint_to_vint:
  forall x y: Z,
    0 <= x < Int.modulus ->
    0 <= y < Int.modulus ->
    Vint (Int.repr x) = Vint (Int.repr y) <-> x = y.
Proof.
  intros; split; intros.
  - inversion H1.
    repeat rewrite Int.Z_mod_modulus_eq in H3.
    rewrite Zmod_small in H3.
    + rewrite Zmod_small in H3; [apply H3 | apply H0].
    + apply H.
  - rewrite H1; reflexivity.
Qed.

Lemma address_mapsto_double_int32:
  forall sh b i d,
    address_mapsto Mfloat64 (Vfloat d) sh (b, Ptrofs.unsigned i) |--
                   predicates_sl.sepcon
                   (address_mapsto Mint32 (Vint (Int64.loword (Float.to_bits d))) sh (b, Ptrofs.unsigned i) )
                   (address_mapsto Mint32 (Vint (Int64.hiword (Float.to_bits d))) sh (b, Ptrofs.unsigned i + 4) ).
Proof.
  intros. unfold address_mapsto. rewrite exp_sepcon1.
  unfold size_chunk_nat in *; unfold size_chunk in *; simpl in *.
  apply exp_left; intros.
  unfold derives; intros.
  (* destruct H as [[[? [? ?]] ?] ?]. *)
  destruct H. destruct H. destruct H. destruct H2.
  (* above two are equivalent, modulo hypothesis names.
     I am keeping yours because the hypothesis names 
     are used below *)

  (*we break x into [m0...m7], then say exists...*)
  assert (exists b0 b1 b2 b3 b4 b5 b6 b7,
             x = [Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; Byte b5; Byte b6; Byte b7]). {
    repeat (destruct x; inversion H).
    rename m6 into m7, m5 into m6, m4 into m5, m3 into m4,
    m2 into m3, m1 into m2, m0 into m1, m into m0.
    destruct m0; inversion H2.
    destruct m1; inversion H2.
    destruct m2; inversion H2.
    destruct m3; inversion H2.
    destruct m4; inversion H2.
    destruct m5; inversion H2.
    destruct m6; inversion H2.
    destruct m7; inversion H2.
    exists i0, i1, i2, i3, i4, i5, i6, i7; reflexivity.
  } 
  
  destruct H4 as [? [? [? [? [? [? [? [? ?]]]]]]]].
  exists [Byte x0; Byte x1; Byte x2; Byte x3].
  rewrite exp_sepcon2.
  exists [Byte x4; Byte x5; Byte x6; Byte x7].



  (* now I need to somehow split the heap *)
  rewrite andp_assoc. rewrite sepcon_andp_prop1.
  rewrite andp_assoc. rewrite sepcon_andp_prop2.
  
  split; [split|].
  - simpl; reflexivity.
  - split; trivial.
    rewrite H4 in H2. unfold decode_val in *. unfold proj_bytes in *. unfold decode_int in *.
    unfold rev_if_be in *. assert (Archi.big_endian = false) by reflexivity. rewrite H5 in *. clear H5.
    unfold int_of_bytes in *. inversion H2. rewrite Float.to_of_bits.
    unfold Int64.loword.
    rewrite (Int.eqm_samerepr
               (Int64.unsigned (Int64.repr
                                  (Byte.unsigned x0 +
                                   (Byte.unsigned x1 +
                                    (Byte.unsigned x2 +
                                     (Byte.unsigned x3 +
                                      (Byte.unsigned x4 +
                                       (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256) * 256) * 256) *
                                    256) * 256)))
               (Byte.unsigned x0 + (Byte.unsigned x1 + (Byte.unsigned x2 + (Byte.unsigned x3 + 0 * 256) * 256) * 256) * 256)
            ). reflexivity.
    rewrite !Int64.unsigned_repr. unfold Int.eqm. unfold Zbits.eqmod. rewrite Int_modulus_value.
    exists (Byte.unsigned x4 + (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256). lia.
    split.
    + repeat (apply Z.add_nonneg_nonneg; [apply Byte_unsigned_range|];
              apply Z.mul_nonneg_nonneg; [|lia]).
      apply Z.add_nonneg_nonneg; [apply Byte_unsigned_range | lia].

    + repeat rewrite Z.mul_add_distr_r.
      assert (255 +
              (255 * 256 +
               (255 * 256 * 256 +
                (255 * 256 * 256 * 256 +
                 (255 * 256 * 256 * 256 * 256 +
                  (255 * 256 * 256 * 256 * 256 * 256 +
                   (255 * 256 * 256 * 256 * 256 * 256 * 256 +
                    (255 * 256 * 256 * 256 * 256 * 256 * 256 * 256 + 0 * 256 * 256 * 256 * 256 * 256 * 256 * 256))))))) =
              Int64.max_unsigned) by (compute; trivial).
      rewrite <- H5. clear H5.
      apply Z.add_le_mono; [apply Byte_unsigned_range2|].
      apply Z.add_le_mono. apply Zmult_lt_0_le_compat_r. lia. apply Byte_unsigned_range2.
      repeat (apply Z.add_le_mono; [repeat apply Zmult_lt_0_le_compat_r; try lia; apply Byte_unsigned_range2|]).
      lia.
  - split.
    + split3; trivial.
      2: apply Z.divide_add_r; trivial; apply Z.divide_refl. 
      
      rewrite H4 in H2. unfold decode_val in *. unfold proj_bytes in *. unfold decode_int in *.
      unfold rev_if_be in *. assert (Archi.big_endian = false) by reflexivity. rewrite H5 in *. clear H5.
      unfold int_of_bytes in *. inversion H2. rewrite Float.to_of_bits.
      unfold Int64.hiword.
      set (j := Int.zwordsize) in *; compute in j; subst j.
      rewrite Int64.shru_div_two_p.
      assert (0 <=
              Byte.unsigned x0 +
              (Byte.unsigned x1 +
               (Byte.unsigned x2 +
                (Byte.unsigned x3 +
                 (Byte.unsigned x4 + (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256) * 256) *
                256) * 256) * 256 <= Int64.max_unsigned). {
        split.
        * apply Z.add_nonneg_nonneg; [apply Byte_unsigned_range|].
          repeat (apply Z.mul_nonneg_nonneg; [apply Z.add_nonneg_nonneg;
                                              [apply Byte_unsigned_range|]|lia]).
          lia.
        * repeat rewrite Z.mul_add_distr_r.
          assert (255 +
                  (255 * 256 +
                   (255 * 256 * 256 +
                    (255 * 256 * 256 * 256 +
                     (255 * 256 * 256 * 256 * 256 +
                      (255 * 256 * 256 * 256 * 256 * 256 +
                       (255 * 256 * 256 * 256 * 256 * 256 * 256 +
                        (255 * 256 * 256 * 256 * 256 * 256 * 256 * 256 + 0 * 256 * 256 * 256 * 256 * 256 * 256 * 256))))))) = Int64.max_unsigned).
          set (j := Int64.max_unsigned) in *; compute in j; subst j. lia. rewrite <- H5. clear H5.
          apply Z.add_le_mono. apply Byte_unsigned_range2.
          apply Z.add_le_mono. apply Zmult_lt_0_le_compat_r. lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          apply Z.add_le_mono. repeat apply Zmult_lt_0_le_compat_r; try lia. apply Byte_unsigned_range2.
          lia.
      }
      rewrite !Int64.unsigned_repr.
      * set (j := two_p 32) in *; compute in j; subst j.
        rewrite <- (Zdiv_unique_full (Byte.unsigned x0 +
                                      (Byte.unsigned x1 +
                                       (Byte.unsigned x2 +
                                        (Byte.unsigned x3 +
                                         (Byte.unsigned x4 + (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256) *
                                         256) * 256) * 256) * 256) 4294967296
                                     (Byte.unsigned x4 + (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256)
                                     (Byte.unsigned x0 +
                                      (Byte.unsigned x1 +
                                       (Byte.unsigned x2 +
                                        (Byte.unsigned x3) * 256) * 256) * 256)).
        -- reflexivity.
        -- unfold Remainder. left. split.
           ++ apply Z.add_nonneg_nonneg. apply Byte_unsigned_range.
              apply Z.mul_nonneg_nonneg. apply Z.add_nonneg_nonneg. apply Byte_unsigned_range.
              apply Z.mul_nonneg_nonneg. apply Z.add_nonneg_nonneg. apply Byte_unsigned_range.
              apply Z.mul_nonneg_nonneg. apply Byte_unsigned_range. lia. lia. lia.
           ++ apply (Z.le_lt_trans (Byte.unsigned x0 + (Byte.unsigned x1 + (Byte.unsigned x2 + Byte.unsigned x3 * 256) * 256) * 256)
                                   (255 + (255 + (255 + 255 * 256) * 256) * 256)).
              apply Z.add_le_mono. apply Byte_unsigned_range2.
              apply Zmult_lt_0_le_compat_r. lia. apply Z.add_le_mono. apply Byte_unsigned_range2.
              apply Zmult_lt_0_le_compat_r. lia. apply Z.add_le_mono. apply Byte_unsigned_range2.
              apply Zmult_lt_0_le_compat_r. lia. apply Byte_unsigned_range2. lia.
        -- lia.
      * split; compute; inversion 1.
      * trivial.
      * rewrite !Int64.unsigned_repr.
        set (j := two_p) in *; compute in j; subst j.
        split. apply Z.div_pos. apply H5. lia.
        apply Zdiv_le_upper_bound. lia.
        apply (Z.le_trans (Byte.unsigned x0 +
                           (Byte.unsigned x1 +
                            (Byte.unsigned x2 +
                             (Byte.unsigned x3 +
                              (Byte.unsigned x4 + (Byte.unsigned x5 + (Byte.unsigned x6 + (Byte.unsigned x7 + 0) * 256) * 256) * 256) * 256) *
                             256) * 256) * 256) Int64.max_unsigned). apply H5. lia.
        set (j := Int64.max_unsigned) in *; compute in j; subst j; lia.
        apply H5.
        
    + (* Use allp_jam_split2? *)
      (* I've no confidence the premises can be solved...*) 

      rewrite <- (allp_jam_split2 (adr_range (b, Ptrofs.unsigned i) 8) (adr_range (b, Ptrofs.unsigned i) 4) (adr_range (b, Ptrofs.unsigned i + 4) 4)
                                  (fun loc : address =>
                                     yesat compcert_rmaps.RML.R.NoneP
                                           (compcert_rmaps.VAL (nth (Z.to_nat (snd loc - Ptrofs.unsigned i)) x Undef)) sh loc)
                                  (fun loc : address =>
                                     yesat compcert_rmaps.RML.R.NoneP
                                           (compcert_rmaps.VAL
                                              (nth (Z.to_nat (snd loc - Ptrofs.unsigned i)) [Byte x0; Byte x1; Byte x2; Byte x3] Undef)) sh loc)
                                  (fun loc : address =>
                                     yesat compcert_rmaps.RML.R.NoneP
                                           (compcert_rmaps.VAL
                                              (nth (Z.to_nat (snd loc - (Ptrofs.unsigned i + 4))) [Byte x4; Byte x5; Byte x6; Byte x7] Undef)) sh loc)
                                  (adr_range_dec (b, Ptrofs.unsigned i) 8)
                 ).
      * split; trivial.
      * eexists. unfold is_resource_pred; intros.
        admit.
      * admit.
      * admit.
      * unfold Ensemble_join. split; intros.
        -- replace 8 with (4+4) by lia.
           apply initial_world.adr_range_divide; lia.
        -- admit.
      * intros. admit.
      * intros. admit.
      * intros. red in k. destruct k.
        -- left; trivial.
        -- exfalso. admit.
        -- right; unfold compcert_rmaps.isFUN; trivial.
           
Abort.
