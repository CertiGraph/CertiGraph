Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.CertiGC.GraphGC.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.CertiGC.env_graph_gc.
Require Import RamifyCoq.floyd_ext.share.

Definition vertex_block_to_fields_body (v: vertex_block): list val := v_fields v.

Definition vertex_block_size (v: vertex_block) := (Z.of_nat (length (v_fields v))).

Definition vertex_block_to_fields_head (v: vertex_block): val :=
  Vint (Int.repr (vertex_block_size v)).

Section sPGG_VST.

  Definition block_rep (sh: share) (p: val) (v: vertex_block) : mpred :=
    data_at sh tint (vertex_block_to_fields_head v)
            (offset_val (-sizeof int_or_ptr_type) p) *
    data_at sh (tarray int_or_ptr_type (vertex_block_size v))
            (vertex_block_to_fields_body v) p.

  Instance PGP_VST (sh: share):
    PointwiseGraphPred val (val * nat) vertex_block unit mpred.
  Proof.
    apply (Build_PointwiseGraphPred _ _ _ _ _ (block_rep sh) (fun _ _ => emp)).
  Defined.

  Lemma sepcon_unique_vertex_at sh:
    writable_share sh -> sepcon_unique2 (@vertex_at _ _ _ _ _ (PGP_VST sh)).
  Proof.
    intros. hnf; intros. simpl.
    unfold block_rep. simpl.
    rewrite <- sepcon_assoc, sepcon_comm. apply sepcon_FF_derives'.
    rewrite sepcon_assoc, sepcon_comm, sepcon_assoc. apply sepcon_FF_derives'.
    rewrite data_at_isptr. Intros. apply data_at_conflict.
    + apply readable_nonidentity, writable_readable. auto.
    + change (sizeof tint) with 4. omega.
  Qed.

  Instance PGA_VST (sh: share): PointwiseGraphAssum (PGP_VST sh).
  Proof. apply (Build_PointwiseGraphAssum _ _ _ _ _ _ _ _ _ _ _). Defined.

  Instance PGAvs_VST (sh: wshare): PointwiseGraphAssum_vs (PGP_VST sh).
  Proof. apply sepcon_unique_vertex_at; auto. Defined.

  Instance PGAvn_VST (sh: wshare): PointwiseGraphAssum_vn (PGP_VST sh) nullval.
  Proof.
    intros [? ?]. simpl. unfold block_rep. rewrite data_at_isptr. normalize.
  Defined.

End sPGG_VST.

Hint Extern 10 (@sepcon_unique2 _ _ _ _ _ (@vertex_at _ _ _ _ _ _)) => apply sepcon_unique_vertex_at; auto.

Instance sPGG_VST (sh: wshare): sPointwiseGraph_GraphGC.
Proof.
  refine (Build_sPointwiseGraph_GraphGC
            _ (PGP_VST sh) (PGA_VST sh) (PGAvs_VST sh) (PGAvn_VST sh)).
Defined.

Global Opaque sPGG_VST.
