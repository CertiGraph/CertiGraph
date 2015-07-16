Class AbsAddr (Addr Val: Type) : Type := mkAbsAddr {
  addr_conflict: Addr -> Addr -> bool;
  addr_empty: Addr -> Prop := fun p => addr_conflict p p = false;
  addr_conflict_comm: forall p1 p2, addr_conflict p1 p2 = addr_conflict p2 p1;
  empty_non_conflict: forall p1 p2, addr_empty p1 -> addr_conflict p1 p2 = false
}.

