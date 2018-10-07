Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export RamifyCoq.CertiGC.gc.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition heap_type: type := Tstruct _heap noattr.
