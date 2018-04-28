(* This file asserts some orders for CompCert types. *)

Require Import RamifyCoq.lib.Coqlib.
Require Import VST.floyd.proofauto. (* It would be nice to trim this down at some point. *)
Require Import RamifyCoq.CertiGC.orders.

Local Open Scope ord.

Lemma ptrofs_int_val_eq: forall i j, Ptrofs.intval i = Ptrofs.intval j -> i = j.
Proof. intros [i] [j]. simpl; intros. apply Ptrofs.mkint_eq. auto. Qed.

Instance ptrofs_ord : Ord ptrofs.
  refine (Build_Ord _ (fun x y => Ptrofs.intval x <= Ptrofs.intval y) _ _ _).
  reflexivity. intros. rewrite H. trivial. intros; apply ptrofs_int_val_eq, ord_antisym; trivial.
Defined.

Instance ptrofs_cord : COrd ptrofs.
Proof.
  intros ? ?. destruct (ord_dec (Ptrofs.intval a) (Ptrofs.intval b)); simpl in *; auto.
Qed.

Instance ptrofs_tord: TOrd ptrofs.
Proof.
  intros ? ?. red. simpl. omega.
Qed.

Instance PV_ord : Ord pointer_val.
Proof.
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
  assert (Ptrofs.intval i <= Ptrofs.intval i1 \/ Ptrofs.intval i1 <= Ptrofs.intval i)%Z by omega.
  destruct H as [[? ?] | [? ?]]; destruct H0 as [[? ?] | [? ?]]; do 2 subst; tauto.
Qed.
