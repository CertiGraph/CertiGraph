Require Export VST.floyd.proofauto.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.sample_mark.garbage_collector.

Local Open Scope logic.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Global Existing Instance CompSpecs.

Definition head_node_type := Tstruct _HeadNode noattr.
Definition content_node_type := Tstruct _ContentNode noattr.

