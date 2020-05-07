Require Export VST.floyd.proofauto.
Require Export RamifyCoq.floyd_ext.closed_lemmas.
(*Require Export RamifyCoq.sample_mark.unionfind_arr.*)
(*There are some side effects with loading this version of unionfind_arr which breaks some parts of the proof*)
Load "./unionfind_arr.v".

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Global Existing Instance CompSpecs.

Definition vertex_type := Tstruct _subset noattr.
