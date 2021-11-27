Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export CertiGraph.floyd_ext.closed_lemmas.
Require Export CertiGraph.unionfind.unionfind.

#[export] Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition node_type := Tstruct _Node noattr.
