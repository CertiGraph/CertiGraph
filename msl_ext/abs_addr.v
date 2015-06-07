Class AbsAddr : Type := mkAbsAddr {
  Addr: Type;
  Val: Type;
  addr_conflict: Addr -> Addr -> bool
}.

Class Alignable (AV: AbsAddr) :=
  addr_alignable: forall p q, p = q \/ addr_conflict p q = true.

Class AddrNonEmpty (AV: AbsAddr) :=
  addr_non_empty: forall p, addr_conflict p p = true.

Implicit Arguments Alignable [].
Implicit Arguments AddrNonEmpty [].
