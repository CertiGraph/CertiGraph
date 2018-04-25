Require Export RamifyCoq.msl_ext.log_normalize.
Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.CertiGC.gc.

Local Open Scope logic.

Global Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.

Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.CertiGC.gc_mathgraph.
Require Import RamifyCoq.lib.Coqlib.

Require Import RamifyCoq.CertiGC.orders.
Require Import RamifyCoq.CertiGC.bounded_numbers.
Require Import RamifyCoq.CertiGC.bitwise_encoding.

Require Import RamifyCoq.CertiGC.cc_orders.
Require Import RamifyCoq.CertiGC.cc_bitwise_encoding.
Require Import RamifyCoq.graph.graph_model.

Definition fieldbits : nat := 22.
Definition tagbits : nat := 8.

Definition fieldnum : Type := boundZ fieldbits.
Definition tagnum : Type := boundZ tagbits.

Definition addr : Type := pointer_val.
Definition null : addr := NullPointer.

Definition maxfields_nat := Z.to_nat (two_power_nat fieldbits).
Definition maxtags_nat := Z.to_nat (two_power_nat tagbits).

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

(* The various magic constants here are from the above diagram. *)
Section MagicConstants.

Instance gc_tc : tagcode (bool * tagnum * fieldnum) :=
  tag_prodswap (tag_boundZ fieldbits) (tag_prod (tag_padleft 1 tag_bool) (tag_boundZ tagbits)).

Instance tc_bitsize_ill : tagint_lossless gc_tc.
Proof. red. trivial. Qed.

End MagicConstants.

Existing Instance gc_tc.

Local Open Scope nat_scope.

Parameter odd : int -> Prop.


Definition valid_data (v : val) : Prop :=
  match v with Vint i => odd i | Vptr b o => False | _ => False end.

Definition data_val : Type := {v : val | valid_data v}.

Definition my_node_rep := @node_rep addr val maxfields_nat tagnum.

Definition nodesize (nr : my_node_rep) : Z :=
  1 + Z.of_nat (length (nr_fields nr)).
(* the fields, plus one word for the header *)

Definition value := tuint. (* this is going to prove inadequate soon. We need to make a decision about what this will actually be. *)

(*
This is where we move from "value" to something more correct.
I'm not sure if my choice of type is correct, though.
Right now it's a pointer to value. That's because, in the C, value = intnat = long.

We'd like the recursive...
Definition node_type (nr : node_rep) : type :=
  tarray (Tpointer node_type noattr) (nodesize nr).

Or even more correctly, we'd like...
Definition node_type (nr : node_rep) : type :=
  tarray (Type_OR (tuint) (Tpointer node_type noattr)) (nodesize nr).

But for now, we settle with what is below...
*)
Definition node_type (nr : node_rep) : type :=
  tarray (Tpointer Tvoid noattr) (nodesize nr).

Local Close Scope nat_scope.

(* if the two addresses are in the same block,
checks that the difference is as proposed *)
Definition size (a1 a2 : addr) (diff : nat) : Prop :=
  match a1, a2 with
  | ValidPointer b1 o1, ValidPointer b2 o2 =>
    b1 = b2 /\ Ptrofs.intval o1 - (Ptrofs.intval o2) = Z.of_nat diff
  | _, _ => False
  end.

Definition env_Graph := @Graph addr _ null _ size val maxfields_nat tagnum.

Local Coercion pg_lg : LabeledGraph >-> PreGraph.
Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition make_nr (g: env_Graph) (v: addr) : my_node_rep.
  remember (vlabel g v) as l.
  refine (Build_node_rep
             (raw_mark l)
             (raw_tag l)
             (fields g v)
             _).
  destruct l.
  unfold fields; rewrite make_fields_length.
  rewrite <- Heql; simpl. apply raw_fieldsbound.
Defined.

Opaque two_power_nat.
(* given a nr, we extract the length of the field and show that it is a fieldnum *)
Program Definition nat_fieldnum (nr : my_node_rep) : fieldnum :=
                    exist _ (Z.of_nat (length (nr_fields nr))) _.
Next Obligation.
  destruct nr. simpl. split.
  - omega.
  - destruct nr_fields_bound.
    clear H.
    unfold maxfields_nat in H0.
    assert (Z.of_nat (Datatypes.length nr_fields) < Z.of_nat (Z.to_nat (two_power_nat fieldbits))) by (apply inj_lt; auto).
    rewrite Z2Nat.id in H. apply H.
    apply two_power_nat_nonneg.
Defined.
Transparent two_power_nat.

Definition followEdge (g: env_Graph) (f : @field addr val) : val :=
  match f with
  | data d => (* proj1_sig *) d
  | pointer e => match (dst g e) with
                 |  ValidPointer blk offset => Vptr blk offset
                 |  NullPointer => Vint (Int.repr 0)
                end
  end.

(* vgamma2cdata + point to that c data *)
(* "vgamma2cdata" was a bit of a misnomer *)
Definition nr2gctc (nr : my_node_rep) : (bool * tagnum * fieldnum) :=
  (nr_color nr, nr_tag nr, nat_fieldnum nr).

Program Definition node_pred (sh: share) (g: env_Graph) (p: addr) (nr : my_node_rep) : mpred :=
  data_at
          sh
          (node_type nr)
          ((Vint (int_of_tag (nr2gctc nr))) ::
           (map (followEdge g) (nr_fields nr)))
          (offset_val (-sizeof value) (pointer_val_val p)).

Instance SGP_VST (sh: share) (g: env_Graph) :
  PointwiseGraphPred addr (addr * nat)  my_node_rep unit mpred.
(* val (and possibly unit) are not obivously correct. see addr and _ in other file *)
refine (@Build_PointwiseGraphPred
          _ _ _ _ _
          (node_pred sh g)
          (fun _ _ => emp)).
Defined.

Instance SGA_VST (sh: share) (g : env_Graph) : @PointwiseGraphAssum addr (addr * nat) _ _ mpred (SGP_VST sh g)
           (@SGBA_GCgraph addr _).
  refine (Build_PointwiseGraphAssum _ _ _ _ _ _ _ _ _ _ _).
Defined.


End pSGG_VST.

Definition my_space := @space addr _.

(* this is a stub of massive proportions; it needs to actually do a BFS or something and get the vertices of the space *)
Definition get_space_vertices (s : space) :=
  (start s) :: (limit s) :: [].

Definition space_size (s : space) :=
  match (start s), (limit s) with
  | ValidPointer b1 o1, ValidPointer b2 o2 => if eq_block b1 b2 then Some (Ptrofs.sub o1 o2) else None
  | _, _ => None
  end.

(* unsigned ok? *)
(* to discuss with Aquinas: having the option int makes sense, but that means that reptype space_type becomes a beast. It's much easier if space_type just always returns a tarray and never a Tvoid. where to compromise? *)
Definition space_type (s: my_space) : type :=
  match (space_size s) with
  | None => Tvoid (* this is trouble *)
  (* | None => tarray (Tpointer Tvoid noattr) 0  *)
  | Some sz => tarray (Tpointer Tvoid noattr) (Ptrofs.intval sz)
  end.

Definition space_type' (s: my_space) : type :=
  tarray (Tpointer Tvoid noattr) 2048.

Definition space_pred' (sh: share) (p: addr) (s: my_space) : mpred :=
  data_at
    sh
    (space_type' s)
    (map pointer_val_val (get_space_vertices s))
    (pointer_val_val p).

(* thought: getting the vertices of the space may not be the way to go. Maybe just make a silly little map from addresses to vertices, making no promises about the vertices. *)
Definition makeverts (Vs : list addr) : list val:=
  repeat Vundef (length Vs).
   