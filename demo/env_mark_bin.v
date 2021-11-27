Require Export VST.floyd.proofauto.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export Demo.mark_bin.

#[global] Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition node_type := Tstruct _Node noattr.
