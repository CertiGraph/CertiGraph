(* This file asserts some orders for CompCert types. *)

Require Import RamifyCoq.lib.Coqlib.
Require Import VST.floyd.proofauto. (* It would be nice to trim this down at some point. *)
Require Import RamifyCoq.CertiGC.orders.

Open Local Scope ord.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

Instance int_ord : Ord int.
  refine (Build_Ord _ (fun x y => Int.unsigned x <= Int.unsigned y) _ _ _).
  reflexivity. intros. rewrite H. trivial. intros; apply unsigned_eq_eq, ord_antisym; trivial.
Defined.

Instance int_cord : COrd int.
Proof.
  intros ? ?. destruct (ord_dec (Int.unsigned a) (Int.unsigned b)); simpl in *; auto.
Qed.

Instance int_tord: TOrd int.
Proof.
  intros ? ?. red. simpl. omega.
Qed.

Instance PV_ord : Ord pointer_val.
  refine (Build_Ord _ (fun x z => match  x,z with 
                        | ValidPointer bx ofsx, ValidPointer bz ofsy => bx = bz /\ ofsx <= ofsy
                        | NullPointer, NullPointer => True
                        | _,_ => False
                       end) _ _ _).
  + intro. icase x. split; reflexivity.
  + intros. icase x; icase y; icase z. destruct H, H0. subst. rewrite H1. auto.
  + intros. icase x; icase y. destruct H, H0. subst b0.
    f_equal. apply ord_antisym; auto.
Defined.

Instance PV_cord: COrd pointer_val.
Proof.
  intros ? ?. icase a; icase b.
  + case (eq_dec b b0).
    * intro. subst b0.
      case (ord_dec i i0). left. simpl. auto.
      right. intro. simpl in H. apply n. tauto.
    * right. intro. simpl in H. destruct H. auto.
  + left. reflexivity.
Qed.

Instance PV_comptrans: ComparableTrans pointer_val.
Proof.
  intros ? ? ?. unfold comparable. simpl; intros.
  icase a; icase b; icase c. 2: destruct H; contradiction.
  assert (Int.unsigned i <= Int.unsigned i1 \/ Int.unsigned i1 <= Int.unsigned i)%Z by omega.
  destruct H as [[? ?] | [? ?]]; destruct H0 as [[? ?] | [? ?]]; do 2 subst; tauto.
Qed.
