Require Import VST.msl.seplog.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.

Class SPATIAL_GRAPH_SET_UP: Type := {
  Data: Type;
  addr: Type;
  addr_eq_dec: forall x y: addr, {x = y} + {x <> y};
  addr_eqb: addr -> addr -> bool := fun x y => if addr_eq_dec x y then true else false
}.

Instance AV_SGraph `{SPATIAL_GRAPH_SET_UP} : AbsAddr.
  apply (mkAbsAddr addr (Data * addr * addr) (fun x y => addr_eqb x y)); simpl; intros.
  + unfold addr_eqb.
    destruct (addr_eq_dec p1 p2), (addr_eq_dec p2 p1); try congruence.
  + unfold addr_eqb in H0.
    destruct (addr_eq_dec p1 p1); congruence.
Defined.

Section SPATIAL_GRAPH.

Variable A: Type.
Variable ND: NatDed A.
Variable SL : SepLog A.
Variable ClSL: ClassicalSep A.
Variable PSL : PreciseSepLog A.
Variable CoSL: CorableSepLog A.
Variable OSL: OverlapSepLog A.
Variable DSL : DisjointedSepLog A.

Variable spatial_graph_set_up: SPATIAL_GRAPH_SET_UP.
Variable trinode : addr -> (Data * addr * addr) -> A.
Variable MSL: MapstoSepLog AV_SGraph trinode.
Variable sMSL: StaticMapstoSepLog AV_SGraph trinode.
Variable nMSL: NormalMapstoSepLog AV_SGraph trinode.

(* Now start proof here. *)

End SPATIAL_GRAPH.

