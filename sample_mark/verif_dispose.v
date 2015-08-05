Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.env_dispose.
Require Import RamifyCoq.graph.graph_model.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_mark.
Require Import RamifyCoq.data_structure.spatial_graph_dispose.

Local Open Scope logic.

Arguments SingleFrame' {l} {g} {s}.

Notation graph sh x g := (@graph _ _ _ _ _ _ (SGP_VST sh) _ x g).
Existing Instances MGS biGraph maGraph finGraph RGF.

Definition mark_spec :=
 DECLARE _mark
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! mark g x g' && graph sh x g')).

Definition spanning_spec :=
  DECLARE _spanning
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; vvalid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`(EX g': Graph, !! spanning_tree g x g' && graph sh x g')).

Definition dispose_spec :=
  DECLARE _dispose
  WITH sh: share, g: Graph, x: pointer_val
  PRE [ _x OF (tptr (Tstruct _Node noattr))]
          PROP  (writable_share sh; weak_valid (pg_gg g) x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (`(!!tree g x && graph sh x g))
  POST [ Tvoid ]
        PROP ()
        LOCAL()
        SEP (`emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := mark_spec :: spanning_spec :: dispose_spec :: main_spec::nil.

Lemma body_mark: semax_body Vprog Gprog f_spanning spanning_spec.
Proof.
  start_function.
  assert (isptr (pointer_val_val x)). admit.
  forward l_old.
Abort.
