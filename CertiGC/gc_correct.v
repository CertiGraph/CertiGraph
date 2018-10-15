Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.shares.
Require Import VST.msl.seplog.
Require Import VST.msl.shares.
Require Import VST.floyd.sublist.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.CertiGC.GCGraph.
Import ListNotations.

Local Open Scope Z_scope.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Class SoundGCGraph (g: LGraph) :=
  {
    field_decided_edges: forall v e,
      vvalid g v -> (src g e = v /\ evalid g e <-> In e (get_edges g v));
    vertex_valid: forall v,  vvalid g v <-> graph_has_v g v
    (* Other constraints would be added later *)
  }.

Definition Graph :=
  GeneralGraph VType EType raw_vertex_block unit graph_info (fun g => SoundGCGraph g).

Local Coercion lg_gg : GeneralGraph >-> LabeledGraph.

Definition injective {A B} (f: A -> B): Prop := forall x y, f x = f y -> x = y.

Definition surjective {A B} (f: A -> B): Prop := forall y, exists x, f x = y.

Definition bijective {A B} (f : A -> B): Prop := injective f /\ surjective f.

Definition graph_iso (g1 g2: PreGraph VType EType)
           (vmap: VType -> VType) (emap: EType -> EType): Prop :=
    bijective vmap /\ bijective emap /\
    (forall v: VType, vvalid g1 v <-> vvalid g2 (vmap v)) /\
    (forall e: EType, evalid g1 e <-> evalid g2 (emap e)) /\
    (forall (e: EType) (v: VType),
        evalid g1 e -> src g1 e = v -> src g2 (emap e) = vmap v) /\
    (forall (e: EType) (v: VType),
        evalid g1 e -> dst g1 e = v -> dst g2 (emap e) = vmap v).

Definition gc_graph_iso (g1: PreGraph VType EType) (roots1: roots_t)
           (g2: PreGraph VType EType) (roots2: roots_t): Prop :=
  let vertices1 := filter_sum_right roots1 in
  let vertices2 := filter_sum_right roots2 in
  exists vmap emap,
    vertices2 = map vmap vertices1 /\
    graph_iso (reachable_subgraph g1 vertices1)
              (reachable_subgraph g2 vertices2) vmap emap.
