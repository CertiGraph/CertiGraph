Require Export RamifyCoq.msl_ext.log_normalize.
Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.ramification.
Require Export RamifyCoq.floyd_ext.semax_ram_lemmas.
Require Export RamifyCoq.floyd_ext.semax_ram_tac.
Require Export RamifyCoq.floyd_ext.exists_trick.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
(* Require Export RamifyCoq.floyd_ext.comparable. *)
Require Export RamifyCoq.CertiGC.gc.

Local Open Scope logic.

Global Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.CertiGC.gc_mathgraph.
Require Import RamifyCoq.lib.Coqlib.

Require Import RamifyCoq.CertiGC.orders.
Require Import RamifyCoq.CertiGC.bounded_numbers.
Require Import RamifyCoq.CertiGC.bitwise_encoding.

Require Import RamifyCoq.CertiGC.cc_orders.
Require Import RamifyCoq.CertiGC.cc_bitwise_encoding.

(* **** *)

Section pSGG_VST.

(* From gc.h, a description of how the objects are laid out in memory.

 31   10 9       8 7        0
      +-------+---------+----------+
      | size  |  color  | tag byte |
      +-------+---------+----------+
v --> |              value[0]      |
      +----------------------------+
      |              value[1]      |
      +----------------------------+
      |                   .        |
      |                   .        |
      |                   .        |
      +----------------------------+
      |           value[size-1]    |
      +----------------------------+
*)

(* The various magic constants below are from the above diagram. *)
Section MagicConstants.

Definition fieldnum : Type := boundZ 22.
Definition tagnum : Type := boundZ 8.

Instance gc_tc : tagcode (bool * tagnum * fieldnum) :=
  prodswap_tc (boundZ_tc 22) (prod_tc (padleft_tc 1 bool_tc) (boundZ_tc 8)).

Instance tc_bitsize_ill : tagint_lossless gc_tc.
Proof. red. trivial. Qed.

End MagicConstants.

Definition addr : Type := pointer_val.
Definition null : addr := NullPointer.

Definition node_rep : Type := bool * list (@field addr val). (* The RHS of spatial graph *)

Definition tag_field (rpa : node_rep) : int :=
  int_of_tag (fst rpa, List.length (snd rpa)).



add_repr:
  forall i j : Z,
  Int.add (Int.repr i) (Int.repr j) =
  Int.repr (i + j)
mul_repr:
  forall x y : Z,
  Int.mul (Int.repr x) (Int.repr y) =
  Int.repr (x * y)
sub_repr:
  forall i j : Z,
  Int.sub (Int.repr i) (Int.repr j) =
  Int.repr (i - j)
repr_inj_unsigned:
  forall i j : Z,
  0 <= i <= Int.max_unsigned ->
  0 <= j <= Int.max_unsigned ->
  Int.repr i = Int.repr j -> i = j

 0 then false else true.

Definition tag_size_Z (sz : Z) : Z := Z.mul tag_size_loc (nodesize rpa).



Definition value := tuint.
Definition node_type (rpa : node_rep) : type := 
  tarray value (nodesize rpa).

D
Definition tag_int (rpa : node_rep) : int :=
  match rpa with
   (b, fl) => Int.repr (Z.mul (nodesize rpa) 1024 + if b then 1 else 0)
  end.
Definition int_tag (t : int) : bool * Z :=
  (Z.div t 1024)

Check .

Definition gcnode (sh: share) (p: addr) (rpa: nat * addr): mpred :=
  data_at sh (node_type (nodesize rpa)) 


node_type (vgamma2cdata rpa) (pointer_val_val p).

Definition fiddle_spec :=
 DECLARE _fiddle
  WITH p: val, n: Z, tag: Z, contents: list Z
  PRE [  ]
          PROP  (Z.div tag 1024 = n)
          LOCAL (temp _p p)
          SEP (data_at Ews (tarray value (1+n)) 
                      (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof value) p))



Definition G := @SG_GCgraph pointer_val _ val.

Print field.
Print reptype.
Print nodesize.

Definition gcnode (sh : share) (p : addr) (rpa : bool * list field) : reptype (node_type (nodesize rpa)).

Definition vgamma2cdata (rpa : bool * list val) : reptype node_type :=
  match rpa with
  | (r, pa) => (Vint (Int.repr (Z.of_nat r)), pointer_val_val pa)
  end.

  Definition binode (sh: share) (p: addr) (rpa: nat * addr): mpred :=
    data_at sh node_type (vgamma2cdata rpa) (pointer_val_val p).



Class pGCgraph : Type := {
  addr : Type;
  null : addr;
  pred : Type;
  SGBA : SpatialGraphBasicAssum addr (addr * nat)
}.

Existing Instance SGBA_GCgraph.

Instance pSGG_VST: pGCgraph.
  refine (Build_pGCgraph pointer_val NullPointer mpred _).
Defined.



Goal 

(*
Instance PointerValE_EqDec: EquivDec.EqDec (pointer_val * nat) eq.
  hnf; intros. destruct x, y. 
  destruct (PV_eq_dec p p0); destruct (nat_eq_dec n n0); subst;
  [left | right..]; try reflexivity; intro; inversion H; contradiction.
Defined.

Instance SGBA_VST: SpatialGraphBasicAssum pointer_val (pointer_val * nat).
  refine (Build_SpatialGraphBasicAssum pointer_val (pointer_val * nat) _ _).
Defined.
*)



End pSGG_VST.

(* In some other file for some reason? *)











Section sSGG_VST.

  Definition binode (sh: share) (p: addr) (rpa: nat * addr): mpred :=
    data_at sh node_type (vgamma2cdata rpa) (pointer_val_val p).

  Instance SGP_VST (sh: share) : SpatialGraphPred addr (addr * unit) (nat * addr) unit pred.
  refine (Build_SpatialGraphPred _ _ _ _ _ (binode sh) (fun _ _ => emp)).
  Defined.

  Instance MSLstandard sh : MapstoSepLog (AAV (SGP_VST sh)) (binode sh).
  Proof.
    intros. apply mkMapstoSepLog. intros.
    apply derives_precise with (memory_block sh (sizeof node_type) (pointer_val_val p)); [| apply memory_block_precise].
    apply exp_left; intros [? ?]. unfold binode. apply data_at_memory_block.
  Defined.

  Lemma sepcon_unique_vertex_at sh: writable_share sh -> sepcon_unique2 (@vertex_at _ _ _ _ _ (SGP_VST sh)).
  Proof.
    intros. hnf; intros. simpl.
    destruct y1 as [? ?], y2 as [? ?].
    unfold binode.
    rewrite data_at_isptr.
    normalize.
    apply data_at_conflict.
    + apply sepalg.nonidentity_nonunit.
      apply readable_nonidentity, writable_readable.
      auto.
    + change (sizeof node_type) with 8.
      apply pointer_range_overlap_refl; auto; omega.
  Qed.

Instance SGA_VST (sh: share) : SpatialGraphAssum (SGP_VST sh).
  refine (Build_SpatialGraphAssum _ _ _ _ _ _ _ _ _ _ _).
Defined.

Instance SGAvs_VST (sh: wshare): SpatialGraphAssum_vs (SGP_VST sh).
  apply sepcon_unique_vertex_at; auto.
Defined.

Instance SGAvn_VST (sh: wshare): SpatialGraphAssum_vn (SGP_VST sh) NullPointer.
  intros [? ?].
  simpl.
  unfold binode.
  rewrite data_at_isptr.
  normalize.
Defined.

End sSGG_VST.

Hint Extern 10 (@sepcon_unique2 _ _ _ _ _ (@vertex_at _ _ _ _ _ _)) => apply sepcon_unique_vertex_at; auto.

Instance sSGG_VST (sh: wshare): @sSpatialGraph_GList pSGG_VST nat unit.
  refine (Build_sSpatialGraph_GList pSGG_VST _ _ (SGP_VST sh) (SGA_VST sh) (SGAvs_VST sh) (SGAvn_VST sh)).
Defined.

Global Opaque pSGG_VST sSGG_VST.


Definition node_type := Tstruct _Node noattr.
