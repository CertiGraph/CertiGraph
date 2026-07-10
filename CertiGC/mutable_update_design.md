# `mutable_update` design decisions

This note records the decisions made before implementing the unfinished
`mutable_update` specification and proof.  It is intentionally a design note,
not a substitute for the Coq definitions.

## Scope

- Verify writes to cells inside `graph_rep` only.  The exterior-cell spec is
  out of scope for now.
- A source field may belong to any generation, including generation 0.  The
  write-barrier contract must not require `vgeneration src <> 0`.
- The source must still be a real, writable, scannable graph field.  Define a
  mutation-specific compatibility predicate equivalent to
  `interior_compatible` without its generation inequality.  In particular it
  retains source-vertex validity, field bounds, `raw_mark = false`, and
  `raw_tag < NO_SCAN_TAG`.
- The new value remains an `exterior_t` and must satisfy the existing
  `exterior_compatible` condition.

## Public and concrete layers

Keep `it : interior_t` as the public logical location because it is already
shared by `interior_address`, `FwdPntIntr`, and `RemSetInterior`.  Since
`InteriorVertexPos` is the only constructor, it contains exactly the same
information as a pair `(src, pos)`.

Use two layers:

```coq
internal_write_at :
  LGraph -> VType -> Z -> exterior_t -> LGraph -> Prop

mutable_graph_update :
  LGraph -> interior_t -> exterior_t -> LGraph -> Prop
```

The public relation just matches `InteriorVertexPos src pos` and delegates to
`internal_write_at g src pos`.

Both relations are concrete graph-transition definitions.  They must not
depend on `sound_gc_graph` or on anything from `gc_correct.v`.

## Concrete graph transition

For a valid position, let:

```coq
e := (src, Z.to_nat pos)
```

The relation distinguishes the following cases in order to reuse existing
graph operations and proofs:

1. The old raw field is `RawInternal` and the new value is
   `ExteriorVertex dst`: use `labeledgraph_gen_dst g e dst` directly.  This
   preserves direct reuse of the existing `lgd_*` algebraic, compatibility,
   and spatial ramification lemmas.
2. The old raw field is not `RawInternal` and the new value is
   `ExteriorVertex dst`: update the source raw field to `RawInternal`, use
   `labeledgraph_add_edge` for `e`, and use `labeledgraph_vgen` for the source
   label.
3. The new value is `ExteriorUnboxed z` or `ExteriorOutlier p`: update the
   source raw field accordingly, remove `e` (removal is harmless if it was not
   valid), and use `labeledgraph_vgen` for the source label.

Introduce a concrete relation such as `raw_vertex_field_update` to state that
the new `raw_vertex_block` has

```coq
raw_fields rvb' = upd_Znth pos (raw_fields rvb) new_raw_field
```

and that its mark, copied vertex, color, and tag are unchanged.  This avoids
putting dependent proof fields from `raw_vertex_block` into the public spec.

The generic graph library already supplies `labeledgraph_vgen`,
`labeledgraph_add_edge`, `pregraph_remove_edge`, and
`labeledgraph_gen_dst`.  Only a thin labeled-graph removal wrapper and the
CertiGC-specific synchronization between `raw_fields` and edges are missing.

## Separation from graph correctness

The transition definition operates on the actual `LGraph` components and the
generic `vvalid`/`evalid` update operations.  It does not assume that
`vvalid = graph_has_v` or `evalid = graph_has_e`.

Preservation is a later theorem in `gc_correct.v`, of the form:

```coq
sound_gc_graph g ->
mutable_graph_update g it new g' ->
(* compatibility of the location and new value *) ->
sound_gc_graph g'.
```

Pure transition definitions belong in `GCGraph.v`; spatial update lemmas
belong in `spatial_gcgraph.v`; soundness preservation belongs in
`gc_correct.v`; `gc_spec.v` should only refer to the public relation.

## Required derived facts

- The transition is deterministic on compatible inputs.
- Vertices, generations, addresses, headers, and all unrelated fields and
  edges are unchanged.
- `sound_gc_graph`, graph/heap compatibility, outlier compatibility, and the
  relevant spatial representations are preserved under their proper
  hypotheses.
- When a write creates a new old-to-young internal edge, recording
  `RemSetInterior it` in remset generation 0 supplies witness `k = 0` for the
  current indexed `no_unrecorded_backward_edge` invariant.

## Mutator/collector pointer handoff

The C program intentionally maintains two phase-specific views of the nursery
allocation/remset boundary:

- while the mutator is running, `ti->alloc` and `ti->limit` are authoritative;
- at entry to `garbage_collect` (and `garbage_collect_all`), those values are
  published to `h->spaces[0].next` and `h->spaces[0].limit`;
- while the collector is running, the space descriptor is authoritative;
- `resume` copies the resulting nursery pointers back to `thread_info`.

Consequently, mutator-phase `before_gc_thread_info_rep` must not require the
possibly stale nursery descriptor's `next` or `limit` fields to equal the
active abstract boundary.  Keep the `thread_info` fields exact, keep
`total_space` exact, and hide both nursery descriptor fields (the representation
already hides `next`; `limit` should be hidden in the same way).  The abstract
`available_space` continues to describe the authoritative mutator boundary and
the split between unused space and the remembered set.

The collector-entry stores establish the full exact heap descriptor before any
collector operation consumes it.  Correctness of this handoff is a spatial
representation fact, not a change to the C collector algorithm.

## Authoritative remset state

For this work, keep the existing `heap` and `thread_info` record definitions
unchanged.  In particular, do not remove `heap.rs_heap`, because doing so would
cause broad, unrelated changes to existing proofs.

Treat the separately supplied `rh : remset_heap` as the sole authoritative
description of remembered-set contents.  It is the state used by
`heap_remset_rep`, the remset correctness invariants, and the collector
relations.  The `rs_heap` stored inside `thread_info.ti_heap` is only a
dependent-record compatibility witness for `pt_heap`; this work does not
require it to equal the external `rh` or preserve the same entries.

This interpretation agrees with the existing garbage-collector proof, which
constructs a new thread-info heap with `build_compatible_heap h` while tracking
the actual remembered set separately as `rh`.

Consequently, the pointer-valued branch of `mutable_update` should:

1. update the authoritative nursery boundary with
   `incr_remset_heap ... 0` in `pt_heap`;
2. rebuild the enclosing `heap` with `build_compatible_heap` (or an equivalent
   compatibility-only constructor), leaving the rest of the thread-info shell
   unchanged; and
3. update the authoritative external remembered set with
   `upd_remset_heap (RemSetInterior it) rh 0`.

The nonpointer branch leaves both the thread info and external `rh` unchanged.

## Funspec boundary

The mutable-update funspec describes a well-formed CertiGC runtime state, so
its PRE includes

```coq
graph_heap_compatible g (pt_heap (ti_heap t_info))
```

This is a justified representation-level condition rather than an optional
global correctness property: the graph objects occupy the generation spaces
described by the heap, and their used/available regions must agree.  Keeping
this condition also permits direct reuse of the existing graph/heap spatial
lemmas.

The PRE also unconditionally requires a recordable nursery,

```coq
used_space nursery < available_space nursery
```

because the C assertion precedes the pointer test, and it requires the
authoritative external remset to match the heap layout:

```coq
remset_heap_and_heap_compatible rh (pt_heap (ti_heap t_info))
```

Together with the previously settled writable-share, mutation-location, and
new-value compatibility conditions, these are the operational and
representation-level premises of the base funspec.

The POST records only the actual deterministic effects:

- `mutable_graph_update g it new g'`;
- the pointer-conditional thread-info/nursery-boundary transition; and
- the pointer-conditional update of external `rh` with
  `RemSetInterior it` in generation 0.

Do not place `sound_gc_graph`, `no_unrecorded_backward_edge`, full
`remset_compatible`, `remset_generation_compatible`, or similar global GC
properties directly in the VST PRE/POST.  Prove them as ordinary conditional
preservation theorems from the transition relation and whatever old invariant
the caller has.  In particular, the mutable-update funspec does not need to
carry `rmst` or `remset_rep`.  Since `mutable_update` has no loop, keeping these
pure arguments outside the VST body proof should remain straightforward and
gives the funspec the weaker, more reusable interface.

### Deferred cleanup (explicitly out of scope)

There is a longer-term modeling cleanup available: remove the redundant
internal `rs_heap`, or redesign the abstract state so that the part heap,
remembered set, and their compatibility proof have exactly one authoritative
owner.  That refactor would change widely used record types and require
substantial reproving.  It is deliberately **not part of the current
`mutable_update` task** and must not be mixed into this implementation.

## Still open

The specification semantics are settled.  The following are implementation
and proof tasks, not remaining design choices:

- implement the settled capacity condition replacing
  `info_recordable := True`;
- implementation of the settled mutator/collector handoff representation and
  the localized repairs to `verif_resume.v` and `verif_garbage_collect.v`;
- implementation of the settled abstract `thread_info` transition currently
  stubbed by `decr_info_nursery`;
- implement the graph transition, spatial update lemmas, and conditional
  preservation theorems;
- registration of the final funspec and the VST body proof.
