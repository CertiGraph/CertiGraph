Require Export RamifyCoq.msl_ext.log_normalize.
Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.semax_ram_lemmas.
Require Export RamifyCoq.floyd_ext.exists_trick.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.floyd_ext.comparable.
Require Export RamifyCoq.floyd_ext.semax_ram_tac.
Require Export RamifyCoq.sample_mark.dispose_bi.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Global Existing Instance CompSpecs.
Global Existing Instance CS_legal.

Definition node_type := Tstruct _Node noattr.
