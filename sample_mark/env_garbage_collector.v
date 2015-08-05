Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.semax_ram_lemmas.
Require Export RamifyCoq.floyd_ext.exists_trick.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.floyd_ext.comparable.
Require Export RamifyCoq.sample_mark.garbage_collector.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Global Existing Instance CompSpecs.
Global Existing Instance CS_legal.

Definition head_node_type := Tstruct _HeadNode noattr.
Definition content_node_type := Tstruct _ContentNode noattr.

