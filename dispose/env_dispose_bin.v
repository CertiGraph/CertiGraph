Require Export CertiGraph.msl_ext.log_normalize.
Require Export VST.floyd.proofauto.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.dispose.dispose_bin.

Local Open Scope logic.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition node_type := Tstruct _Node noattr.
