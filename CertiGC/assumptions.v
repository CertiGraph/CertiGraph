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
   mutable_update_gc_ready,
   mutable_update_gc_sep,
   remset_rep_mutable_graph_update).

(** CompCert [extcall_properties] for separate external-call models of
    [Is_from] and [test_int_or_ptr], not [semax_body] proofs of their
    internal Clight implementations. *)
Definition extcall_endpoints :=
  (Is_from_extcall, test_iop__extcall).

(** Three internal functions specified in [Gprog] have no [semax_body]
    proof: [test_int_or_ptr], [Is_from], and [abort_with]. *)
Definition audit_collection :=
  (verified_bodies, model_endpoints, extcall_endpoints).

Print Assumptions audit_collection.
