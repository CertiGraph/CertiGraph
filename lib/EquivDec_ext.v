Require Export Coq.Classes.EquivDec.

Ltac destruct_eq_dec a b :=
  let H := fresh "H" in
  destruct (@EquivDec.equiv_dec _ eq _ _ a b) as [H | H]; unfold complement, eq_equivalence, equiv in H.

Close Scope equiv_scope.
