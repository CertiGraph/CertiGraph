Require Import compcert.lib.Coqlib compcert.lib.Zbits.
Require Import compcert.common.AST compcert.lib.Integers.
Require Import compcert.common.Values compcert.common.Memory.
Require Import compcert.common.Globalenvs compcert.common.Events.

Inductive int_or_ptr: val -> mem -> val -> Prop :=
  | int_or_ptr_int: forall n m,
      Int.and n Int.one = Int.one ->
      int_or_ptr (Vint n) m Vfalse
  | int_or_ptr_ptr: forall b ofs m,
      Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + 2) Cur Nonempty ->
      Ptrofs.and ofs Ptrofs.one = Ptrofs.zero ->
      int_or_ptr (Vptr b ofs) m Vtrue.

Remark ptrofs_2_aligned: forall ofs,
  Ptrofs.and ofs Ptrofs.one = Ptrofs.zero <-> (2 | Ptrofs.unsigned ofs).
Proof.
  assert (A: forall n, (2 | n) <-> Z.Even n).
  { intros; split; intros [k E]; rewrite E; exists k; ring. }
  assert (B: forall n, Z.Even n <-> Z.testbit n 0 = false).
  { intros. rewrite Z.bit0_odd, <- Z.negb_even, <- Z.even_spec, negb_false_iff. tauto. }
  intros; split; intros.
- apply A. apply B. change false with (Ptrofs.testbit Ptrofs.zero 0). rewrite <- H. 
  rewrite Ptrofs.bits_and, Ptrofs.bits_one. simpl. rewrite andb_true_r; auto.
  generalize Ptrofs.wordsize_pos; omega.
- apply A in H. apply B in H. Ptrofs.bit_solve. rewrite Ptrofs.bits_one.
  destruct (zeq i 0); simpl. 
  rewrite andb_true_r. subst i. exact H.
  apply andb_false_r.
Qed.

Lemma int_or_ptr_inject:
  forall v m res f v' m',
  int_or_ptr v m res ->
  Val.inject f v v' ->
  Mem.inject f m m' ->
  exists res', int_or_ptr v' m' res' /\ Val.inject f res res'.
Proof.
  destruct 1; intros VI MI; inv VI.
- (* integer *)
  exists Vfalse; split.
+ constructor; auto.
+ constructor.
- (* pointer *)
  assert (AL: (2 | delta)).
  { change 2 with (align_chunk Mint16unsigned). clear H0. 
    eauto using Mem.mi_align, Mem.mi_inj, Mem.range_perm_max. }
  assert (OF: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) = Ptrofs.unsigned ofs + delta).
  { eapply Mem.address_inject; eauto. apply H. omega. }
  exists Vtrue; split.
+ constructor.
* rewrite OF. replace (Ptrofs.unsigned ofs + delta + 2) with ((Ptrofs.unsigned ofs + 2) + delta) by omega.
  eapply Mem.range_perm_inject; eauto.
* apply ptrofs_2_aligned in H0. apply ptrofs_2_aligned. rewrite OF. 
  apply Z.divide_add_r; auto.
+ constructor.
Qed.
