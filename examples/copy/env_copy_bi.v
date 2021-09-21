Require Export VST.floyd.proofauto.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.floyd_ext.share.
Require Export CertiGraph.copy.copy_bi.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Global Existing Instance CompSpecs.

Definition node_type := Tstruct _Node noattr.
