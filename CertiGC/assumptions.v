From CertiGraph.CertiGC Require Import
  verif_garbage_collect
  verif_create_heap
  verif_create_space
  verif_do_generation
  verif_do_scan
  verif_forward_remset
  verif_forward_roots
  verif_forward
  verif_make_tinfo
  verif_conversion
  verif_is_ptr
  verif_resume
  verif_mutable_update
  verif_Is_from
  spatial_gcgraph
  gc_correct.

(** VST proofs of the sixteen verified internal Clight function bodies. *)
Definition verified_bodies :=
  (body_garbage_collect,
   body_create_heap,
   body_create_space,
   body_do_generation,
   body_do_scan,
   body_forward_remset,
   body_forward_roots,
   body_forward,
   body_make_tinfo,
   body_int_to_int_or_ptr,
   body_int_or_ptr_to_int,
   body_ptr_to_int_or_ptr,
   body_int_or_ptr_to_ptr,
   body_is_ptr,
   body_resume,
   body_mutable_update).

(** Model-level and spatial correctness endpoints used when auditing the
    collector and the mutable-update boundary. *)
Definition model_endpoints :=
  (garbage_collect_spec_preconditions_imply_isomorphism,
   mutable_graph_update_sound,
   mutable_update_garbage_collect_model_preconditions,
   int_mutable_update_restores_garbage_collect_model_preconditions,
   remset_rep_mutable_graph_update).

(** These results establish [extcall_properties] for legacy external-call
    semantics.  They are not [semax_body] proofs of the corresponding
    internal Clight functions in [Gprog]. *)
Definition legacy_extcall_endpoints :=
  (Is_from_extcall, test_iop__extcall).

(** In particular, [Gprog] currently has no [body_test_int_or_ptr],
    [body_Is_from], or [body_abort_with] theorem.  The legacy extcall results
    above do not close those internal-function body-proof obligations. *)
Definition audit_collection :=
  (verified_bodies, model_endpoints, legacy_extcall_endpoints).

Print Assumptions audit_collection.
