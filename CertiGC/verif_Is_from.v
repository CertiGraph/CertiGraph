
(******************************)
(*                            *)
(*          CONTENTS          *)
(*                            *)
(* is_from          line  20  *)
(* int_or_ptr, v1   line 280  *)
(* int_or_ptr, v2   line 355  *) 
(*                            *)
(******************************)

Require Import compcert.common.Events compcert.common.Memory.
Require Import compcert.common.Values compcert.common.AST.
Require Import compcert.x86_32.Archi compcert.lib.Integers.
Require Import Coq.ZArith.BinInt Coq.Lists.List Omega.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.


(* Verification of the function Is_from *)

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
      exists n : Z, 0 < n /\
                    Ptrofs.unsigned o1 + n < Int.modulus /\
                    b1 = b2 /\
                    Ptrofs.unsigned o1 + n = Ptrofs.unsigned o2 /\
                    valid_block m1 b1 o1 n /\
                    common.Memory.Mem.valid_pointer m1 b3 (Ptrofs.unsigned o3) = true /\
                    ((b1 = b3 /\
                      Ptrofs.unsigned o1 <= Ptrofs.unsigned o3 < Ptrofs.unsigned o2 /\
                      ret = Vone) \/
                     ((b1 <> b3 \/
                       (b1 = b3 /\
                        (Ptrofs.unsigned o3 < Ptrofs.unsigned o1 \/
                         Ptrofs.unsigned o3 >= Ptrofs.unsigned o2)))
                      /\ ret = Vzero))
    | _ => False
    end.

Definition Is_from_sig : signature :=
  mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default.

Ltac split3 := split; [|split ].

Lemma lt_ptr_mod: forall n1 n2,
    n1 <= n2 <= Ptrofs.max_unsigned ->
    n1 <= n2 < Ptrofs.modulus.
Proof. 
  intros.
  replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by
      (unfold Ptrofs.max_unsigned; omega).
  now rewrite <- Z.lt_le_pred in *.
Qed.

Lemma Is_from_extcall: extcall_properties Is_from_sem Is_from_sig.
Proof.
  constructor; intros.
  - destruct H as [_ [_ ?]].
    do 4 (destruct vargs; try destruct v; try contradiction).
    destruct H as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    destruct H as [[_ [_ ?]] | [_ ?]]; subst; apply I.
  - apply H0.
  - destruct H as [? _]. subst m1. trivial. 
  - destruct H as [? _]. subst m1. trivial. 
  - destruct H as [? _]. subst m1; apply Mem.unchanged_on_refl.
  - exists vres, m1'.
    destruct H as [? [? ?]]; subst m2 t.
    split.      
    2: split3; [apply Val.lessdef_refl | trivial | apply Mem.unchanged_on_refl].
    split3; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).    
    inversion H1; inversion H4; inversion H6; inversion H11;
      inversion H13; inversion H18; inversion H20; subst.
    clear H4 H11 H18 H20 H13 H6 H1.
    destruct H3 as [n [? [? [? [? ?]]]]].
    exists n. do 4 (split; trivial).
    clear -H0 H4. destruct H4 as [? [? ?]].
    split3; [|eapply Mem.valid_pointer_extends; eauto | tauto].
    destruct H as [? [? ?]].
    do 2 (split; trivial).
    intros. specialize (H4 i2 H5).
    eapply Mem.valid_pointer_extends; eauto.
  - intros. exists f, vres, m1'. destruct H0 as [? [? ?]]. split.
    2: {
      split.
      - clear -H4.
        do 4 (destruct vargs; try destruct v; try contradiction).
        destruct H4 as [_ [_ [_ [_ [_ [_ [_ H]]]]]]].
        destruct vres; auto. now destruct H. 
      - repeat (split; [now subst|]). congruence.
    }
    split3; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).
    inversion H2; inversion H7; inversion H9;
      inversion H17; inversion H19; inversion H27; inversion H29; subst.
    clear H2 H7 H9 H17 H19 H27 H29.
    destruct H4 as [n [? [? [? [? [? [? ?]]]]]]].
    exists n. rewrite H3 in  H12; rewrite H22 in H12; inversion H12.
    subst; clear H12.
    assert (Hf: 0 <= Ptrofs.unsigned i + n < Ptrofs.modulus) by
        (rewrite H4; apply Ptrofs.unsigned_range).
    assert (Ha: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta)) + n < Int.modulus). {
      replace Int.modulus with Ptrofs.modulus by
          (unfold Int.modulus, Ptrofs.modulus; f_equal).
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep b0 b3 delta
                      (Ptrofs.add i (Ptrofs.repr n)) H22) as [Hx Hy]. 
      { right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]].
        assert (Hm: 0 <= n - 1 < n) by omega; rewrite <- (H5 _ Hm).
        f_equal; unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
      }
      clear -Hx Hy Hf H0.
      apply lt_ptr_mod in Hy. unfold Ptrofs.add in *. 
      repeat rewrite Ptrofs.unsigned_repr_eq in *.
      rewrite Z.add_mod_idemp_r, Z.mod_small in * by easy.
      rewrite Z.mod_small; [omega|]. 
      destruct i. unfold Ptrofs.unsigned in *; simpl in *. omega.
    }
    split3; [| |split3; [| |split3]]; trivial.
    + destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta
                   (Ptrofs.add i (Ptrofs.repr n)) H22) as [Hd' Hd]. {
        right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]]. assert (0 <= n - 1 < n) by omega.
        rewrite <- (H5 _ H1). f_equal.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
      }
      unfold Ptrofs.add. rewrite <- H4.
      destruct (Ptrofs.unsigned_range i) as [? _].
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Z.add_mod_idemp_r by easy.
      replace Int.modulus with Ptrofs.modulus in Ha by
          (unfold Int.modulus, Ptrofs.modulus; f_equal).
      unfold Ptrofs.add in Hd.
      repeat rewrite Ptrofs.unsigned_repr_eq in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small in Hd by easy.
      apply lt_ptr_mod in Hd.
      repeat rewrite Z.mod_small; [omega | trivial | omega].
    + split3; [easy | omega|]. intros.
      destruct H5 as [_ [_ H5]].
      rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H22 H1 (H5 i2 H3)).
      f_equal. unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta i H22) as [_ Hd]. {
        left. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        assert (0 <= 0 < n) by omega; rewrite <- (H5 0 H1); f_equal; omega.
      } 
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
    + rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H32 H1 H6).
      f_equal. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta1 i1 H32) as [_ Hd]. {
        left; now apply Mem.perm_cur_max,
              Mem.valid_pointer_nonempty_perm.
      }
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
    + destruct H7.
      * destruct H3 as [? [? ?]]; subst b1 vres.
        destruct H1 as [_ _ _ _ rep _].
        destruct (rep b0 b3 delta i H22) as [_ Hp]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          destruct H5 as [_ [_ H5]]; assert (0 <= 0 < n) by omega.
          specialize (H5 0 H1).
          now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H5 by omega.
        }
        destruct (rep b0 b3 delta i1 H22) as [_ Hq]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
            destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega.
          specialize (H1 0 H3); now rewrite H6.
        }
        destruct (rep b0 b3 delta i0 H22) as [_ Hr]. {
          destruct H5 as [_ [_ H5]]. rewrite <- H4.
          assert (Hm: 0 <= n - 1 < n) by omega.
          right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          rewrite <- (H5 _ Hm); f_equal; omega.
        }
        rewrite H22 in H32; inversion H32.
        left. split3; trivial.
        subst delta1. clear -H7 Hp Hq Hr.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr.  
        repeat rewrite Z.add_mod_idemp_r, Z.mod_small by easy.
        omega.
      * destruct H3. right. split; trivial.
        rename m2 into m; rename m1' into m'.
        destruct H1 as [_ _ _ lap rep _].
        destruct H3.
        -- destruct (eq_block b3 b7); [|now left].
           subst b3. right. split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           destruct H5 as [_ [_ H5]].
           assert (0 <= 0 < n) by omega.
           pose proof (H5 _ H3).
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H6.
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H8.
           replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H8 by omega.
           destruct (rep _ _ delta1 i1 H32) as [_ Hp]; [left; easy|].
           destruct (rep _ _ delta i H22) as [_ Hq]; [left; easy|].
           destruct (rep _ _ delta i0 H22) as [_ Hr]. {
             rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             specialize (H5 _ Hm).
             replace (Ptrofs.unsigned i + (n - 1)) with (Ptrofs.unsigned i + n - 1) in H5 by omega.
             apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H5. now right.
           }
           replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by
               (unfold Ptrofs.max_unsigned; omega).       
           rewrite <- Z.lt_le_pred in *.
           repeat rewrite Z.mod_small by easy.
           destruct (lap _ _ _ _ _ _ _ _ H1 H22 H32 H8 H6); [contradiction|].
           clear rep Hp Hq Hr.
           replace (Ptrofs.unsigned i) with ((Ptrofs.unsigned i - delta) + delta) in H5 by omega.
           assert ((Ptrofs.unsigned i1 + delta1 < Ptrofs.unsigned i + delta) \/
                   (Ptrofs.unsigned i1 + delta1 >= Ptrofs.unsigned i0 + delta) \/
                   ((Ptrofs.unsigned i1 + delta1 >= Ptrofs.unsigned i + delta) /\
                    Ptrofs.unsigned i1 + delta1 < Ptrofs.unsigned i0 + delta)) by omega.
           destruct H10; [auto | destruct H10; [auto|]].
           exfalso.
           destruct H10. rewrite <- H4 in H11.
           assert (0 <= Ptrofs.unsigned i1 + delta1 - Ptrofs.unsigned i - delta < n) by omega.
           specialize (H5 (Ptrofs.unsigned i1 + delta1 - Ptrofs.unsigned i - delta) H12).
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H5.
           destruct (lap b0 b7 delta b1 b7 delta1 _ (Ptrofs.unsigned i1) H1 H22 H32 H5 H6); [auto | apply H13; omega].
        -- destruct H1. subst b0 vres.
           right. rewrite H22 in H32; inversion H32.
           clear H32.
           split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           subst delta1.           
           destruct (rep b1 b3 delta i H22) as [_ Hp]. {
             left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             destruct H5 as [_ [_ H5]]; assert (H1: 0 <= 0 < n) by omega.
             specialize (H5 0 H1).
             now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H5 by omega.
           }
           destruct (rep b1 b3 delta i1 H22) as [_ Hq].
           1:  now left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
           destruct (rep b1 b3 delta i0 H22) as [_ Hr]. {
             destruct H5 as [_ [_ H5]]. rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             rewrite <- (H5 _ Hm); f_equal; omega.
           }
           clear - H3 Hp Hq Hr.
           apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr. 
           repeat rewrite Z.mod_small by easy.
           destruct H3; [left | right]; omega.
  - intros. destruct H as [_ [? _]]. subst t. simpl. omega.
  - intros. generalize H. destruct H as [_ [? _]]. subst t1.
    inversion H0. subst t2. clear H0. intro H.
    exists vres1, m1. apply H.
  - intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
    subst m1 m2 t1 t2. split; [constructor|].
    intros _. split; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).
    destruct H2 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    destruct H4 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    intuition; congruence.
Qed.



(* Verification of the function test_int_or_ptr, version 1 *)

(* 
 * This version does not include the check for (b, ofs) and (b, ofs+1).
 * It's mostly meant to show the naive failure case.
 *)

Definition test_iop_sem : extcall_sem :=
  fun _ args m1 trc ret m2 =>
    m1 = m2 /\ trc = nil /\
    match args with
    | [Vint i] =>
      ret = Vint (Int.modu i (Int.repr 2))
    | [Vptr b ofs] =>
      ret = Vint (Ptrofs.to_int (Ptrofs.modu ofs (Ptrofs.repr 2)))
    | _  => False
    end.

Definition test_iop_sig : signature :=
  mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default.

Lemma test_iop__extcall: extcall_properties test_iop_sem test_iop_sig.
Proof.
  constructor; intros.
  - destruct H as [_ [_ ?]].
    do 2 (destruct vargs; try destruct v; try contradiction); subst; apply I.
  - apply H0.
  - destruct H as [? _]. subst m1. trivial. 
  - destruct H as [? _]. subst m1. trivial.
  - destruct H as [? _]. subst m1. apply Mem.unchanged_on_refl.
  - exists vres, m1'.
    destruct H as [? [? ?]]. subst m2 t.
    split.
    2: split3; [apply Val.lessdef_refl | trivial | apply Mem.unchanged_on_refl]. 
    split3; trivial.
    do 2 (destruct vargs; try destruct v; try contradiction);
      inversion H1; inversion H4; inversion H6; auto.
  - (* ec_mem_inject *)
    exists f, vres, m1'.
    destruct H0 as [? [? ?]]; subst.
    split.
    2: {
      split.
      - do 2 (destruct vargs; try destruct v; try contradiction); subst; constructor.
      - split; [trivial|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply inject_incr_refl|].
        congruence.
    }
    split3; trivial.
    do 2  (destruct vargs; try destruct v; try contradiction).
    + inversion H2; inversion H5; inversion H7; trivial.
    + inversion H2; inversion H5; inversion H7; subst.
      (* We have reason to believe that i is even, but we don't 
       * know anything useful about delta. On the face of it, 
       * delta need not be even. The hypothesis H1, Mem.inject, is the
       * obvious place to look for help. I studied it carefully. 
       * It has statements involving delta, but never comments 
       * on delta's parity. I think we're dead.
       *)
      admit.
  - intros. destruct H as [_ [? _]]. subst t. simpl; omega.
  - intros. generalize H. destruct H as [_ [? _]].
    subst t1; inversion H0; subst t2.
    intro H; exists vres1, m1; apply H.
  - intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
    subst m1 m2 t1 t2.
    split; [constructor|].
    intros _. split; trivial.
    do 2 (destruct vargs; try destruct v; try contradiction); congruence.
Admitted.



(* Verification of the function test_int_or_ptr, version 2 *)

(* 
 * Ref: Xavier's email on Nov 10 2018,
 * We are checking both o and the successor of o 
 *)

Definition valid_b_o_So (m : mem) (b : block) (o : ptrofs) : Prop :=
  Mem.perm m b (Ptrofs.unsigned o) Max Nonempty /\
  Mem.perm m b ((Ptrofs.unsigned o) + 1) Max Nonempty.


Lemma valid_b_o_So_dec: forall m b o, {valid_b_o_So m b o} + {~ valid_b_o_So m b o}.
Proof.
  intros. unfold valid_b_o_So.
  destruct (Mem.perm_dec m b (Ptrofs.unsigned o) Max Nonempty), (Mem.perm_dec m b (Ptrofs.unsigned o + 1) Max Nonempty).
  - left; auto. 
  - right; intros [_ ?]; contradiction.
  - right; intros [? _]. apply n; contradiction.
  - right; intros [? _]. contradiction. 
Qed.

(* 
 * I know this is ugly and leads to a clunky proof, but I'm just 
 * trying to show you the computation very explicitly. 
 * Details are in Xavier's email from November. 
 *)
Definition test_iop_sem' : extcall_sem :=
  fun _ args m1 trc ret m2 =>
    m1 = m2 /\ trc = nil /\ 
    match args with
    | [Vint i] =>
      if (Int.eq Int.one (Int.modu i (Int.repr 2)))
      then ret = Vone
      else False
    | [Vptr b ofs] =>
      if (Ptrofs.eq Ptrofs.one (Ptrofs.modu ofs (Ptrofs.repr 2)))
      then False
      else if valid_b_o_So_dec m1 b ofs                    
           then ret = Vzero
           else False
    | _ => False
    end.

(* No change from before, just pasting again to make this section standalone *)
Definition test_iop_sig' : signature :=
  mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default.

Lemma test_iop__extcall': extcall_properties test_iop_sem' test_iop_sig'.
Proof.
  constructor; intros.
  - destruct H as [_ [_ ?]].
    destruct vargs; try destruct v; try contradiction.
    + destruct vargs; [|contradiction].
      destruct (Int.eq Int.one (Int.modu i (Int.repr 2))); subst; easy.
    + destruct vargs; [|contradiction].
      destruct (Ptrofs.eq Ptrofs.one (Ptrofs.modu i (Ptrofs.repr 2))); [contradiction|].
      destruct (valid_b_o_So_dec m1 b i); subst; easy.
  - apply H0.
  - destruct H as [? _]. subst m1. trivial. 
  - destruct H as [? _]. subst m1. trivial.
  - destruct H as [? _]. subst m1. apply Mem.unchanged_on_refl.
  - destruct H as [? [? ?]]. subst m2 t.
    exists vres, m1'. split.
    2: split3; [apply Val.lessdef_refl | trivial | apply Mem.unchanged_on_refl].
    split3; trivial.
    do 2 (try destruct vargs; try destruct v); try contradiction;
      inversion H1; inversion H4; inversion H6; auto.
    clear -H0 H3.
    (* 
     * Basically we need to show that the valid_b_o_So in the hypothesis
     * implies the valid_b_o_So in the goal. Luckily, it does. 
     * When refactoring, I may extract this to a separate lemma, but
     * for now I'll just strip away the details until the core goal is exposed. 
     *)
    destruct (Ptrofs.eq Ptrofs.one (Ptrofs.modu i (Ptrofs.repr 2))); auto.
    destruct (valid_b_o_So_dec m1 b i); 
      destruct (valid_b_o_So_dec m1' b i); [trivial| | contradiction..].
    clear H3; destruct n. (* There we go, the core goal. *)
    destruct H0 as [_ [? _ _] _]. (* And this is going to save us. *)
    assert (inject_id b = Some (b, 0)) by now unfold inject_id.
    unfold valid_b_o_So in *; destruct v; split.
    + specialize (mi_perm b b 0 (Ptrofs.unsigned i) Max Nonempty H H0).
      replace (Ptrofs.unsigned i + 0) with
          (Ptrofs.unsigned i) in mi_perm by omega.
      trivial.
    + specialize (mi_perm b b 0 (Ptrofs.unsigned i + 1) Max Nonempty H H1).
      replace (Ptrofs.unsigned i + 1 + 0) with
          (Ptrofs.unsigned i + 1) in mi_perm by omega.
      trivial.
  - 
    (** External calls must commute with memory injections,
  in the following sense. *)
(*  ec_mem_inject:
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
    intros. exists f, vres, m1'.
    (* 
     * A possible misstep is my choice of "f" as the meminj.
     * I've searched the CompCert codebase for instances of "extcall properties" 
     * being used (all of these instances are in CompCert/common/Events.v).
     * The original f is often piped back in as the meminj in many cases.
     * A new meminj is cooked up sometimes, 
     * but I don't believe those cases are similar to ours.
     * A SearchAbout on meminj shows that there aren't all that many ways to 
     * create a new meminj... let's go on ahead for now.
     *)
    destruct H0 as [? [? ?]]. subst.
    split.
    2: {
      split.
      - destruct vres; auto.
        do 2 (destruct vargs; try destruct v; try contradiction).
        + destruct (Int.eq Int.one (Int.modu i0 (Int.repr 2))); [inversion H4 | easy]. 
        + destruct (Ptrofs.eq Ptrofs.one (Ptrofs.modu i0 (Ptrofs.repr 2))); try contradiction.
          destruct (valid_b_o_So_dec m2 b0 i0); [inversion H4 | easy].
      - split; [trivial|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply inject_incr_refl|].
        congruence.
    }
    split3; trivial.
    do 2 (destruct vargs; try destruct v; try contradiction).
    + inversion H2. inversion H5. inversion H7. auto.
    + inversion H2. inversion H5. inversion H7.
      (* 
       * This is where we died in version 1. 
       * Let's keep going, we can strip away a few more layers... 
       *)
      subst; clear H7 H2.
      destruct (Ptrofs.eq Ptrofs.one (Ptrofs.modu i (Ptrofs.repr 2))) eqn:parity1; [contradiction|].
      destruct (valid_b_o_So_dec m2 b i); [|contradiction].
      destruct (Ptrofs.eq Ptrofs.one
                          (Ptrofs.modu (Ptrofs.add i (Ptrofs.repr delta)) (Ptrofs.repr 2))) eqn:parity2.
      * (*
         * From parity1 we know that i was even. 
         * We need a contradiction from parity2.
         
         * By digging into Mem.inject, I can show that 
         * delta's range is within Ptrofs.modulus.
         * From there I can show that the Ptrofs.add in "parity2" will 
         * work out fine and we'll just have "(i+delta) mod 2 = 1" in "parity2".
         * For an example of this manipulation in action, 
         * please see lines 520-529 below.
         
         * Anyway so after this manipulation, that we must get a 
         * contradition from "parity2", which means showing that delta is odd.
         * Alternately, this means showing that i and delta have opposite parities.
         * This is the same issue we had in version 1.
         * Again, I explored Mem.inject, which deals with delta a fair bit.
         * Sadly, it doesn't enforce anything about delta's parity.
         * I think we're dead once again.
         *)
        admit. 
      * destruct (valid_b_o_So_dec m1' b2 (Ptrofs.add i (Ptrofs.repr delta))); auto.
        destruct n.
        destruct H1 as [[? _ _] _ _ _ rep _].
        clear - mi_perm v H10 rep.
        unfold valid_b_o_So in *.
        destruct v; split.
        -- specialize (mi_perm _ _ _ (Ptrofs.unsigned i) Max Nonempty H10 H).
           replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) with
               (Ptrofs.unsigned i + delta).
           2: {
             destruct (rep _ _ delta i H10).
             1: left; trivial. 
             unfold Ptrofs.add.
             repeat rewrite Ptrofs.unsigned_repr_eq.
             rewrite Z.add_mod_idemp_r by easy.
             apply lt_ptr_mod in H2. 
             rewrite Z.mod_small by easy. trivial. 
           }
           trivial.
        -- specialize (mi_perm _ _ _ (Ptrofs.unsigned i + 1) Max Nonempty H10 H0).
           replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta)) + 1) with (Ptrofs.unsigned i + 1 + delta).
            2: {
              destruct (rep _ _ delta i H10).
              left; trivial. 
              unfold Ptrofs.add.
              repeat rewrite Ptrofs.unsigned_repr_eq.
              rewrite Z.add_mod_idemp_r by easy.
              apply lt_ptr_mod in H2.
              rewrite Z.mod_small by easy. omega.
            }
            trivial.
  - destruct H as [_ [? _]]. subst t. simpl; omega.
  - generalize H. destruct H as [_ [? _]].
    subst t1; inversion H0; subst t2.
    intro H; exists vres1, m1; apply H.
  - destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
    subst m1 m2 t1 t2.
    split; [constructor|]. intros _. split; trivial.
    do 2 (try destruct vargs; try destruct v; try contradiction).
    + destruct (Int.eq Int.one (Int.modu i (Int.repr 2))); subst; [trivial | contradiction].
    + destruct (Ptrofs.eq Ptrofs.one (Ptrofs.modu i (Ptrofs.repr 2))); [contradiction|].      
      destruct (valid_b_o_So_dec m b i); [|contradiction].
      subst; trivial.
Admitted.
