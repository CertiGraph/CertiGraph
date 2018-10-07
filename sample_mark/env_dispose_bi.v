Require Export RamifyCoq.msl_ext.log_normalize.
Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
Require Export RamifyCoq.sample_mark.dispose_bi.

Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Global Existing Instance CompSpecs.

Definition node_type := Tstruct _Node noattr.
