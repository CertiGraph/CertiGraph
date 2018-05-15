Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export RamifyCoq.CertiGC.gc.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition heap_type: type := Tstruct _heap noattr.

Definition fun_info_rep (sh: share) (l: list Z) (p: val) : mpred :=
  data_at sh (tarray tuint (Zlength l + 1))
          (map Vint (map Int.repr (Zlength l :: l))) p.
