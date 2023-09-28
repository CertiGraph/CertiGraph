Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export CertiGraph.CertiGC.gc.

(* BEGIN these patches are necessary for VST 2.12 with Coq 8.17,
   but should no longer be necessary in VST 2.13 and beyond *)
Ltac quick_typecheck3 ::=
 apply quick_derives_right; go_lowerx; intros;
 repeat apply andp_right; auto; fail.

Ltac default_entailer_for_load_store ::=
  try quick_typecheck3;
  unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
  try solve [entailer!].
(* END these patches are necessary for VST 2.12 with Coq 8.17 *)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition heap_type: type := Tstruct _heap noattr.
