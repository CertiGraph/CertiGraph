From CertiGraph.CertiGC Require Import 
  verif_garbage_collect
  verif_create_heap
  verif_create_space
  verif_do_generation
  verif_do_scan
  verif_forward_remset
  verif_forward_roots
  verif_forward
  verif_make_tinfo
   gc_correct.

Definition collection := 
(body_garbage_collect,
 body_create_heap,
 body_create_space,
 body_do_generation,
 body_do_scan,
 body_forward_remset,
 body_forward_roots,
 body_forward,
 body_make_tinfo,
 garbage_collect_spec_preconditions_imply_isomorphism).
 

Print Assumptions collection.

(* Print Assumptions produces the following list:
 Part 1, standard extensionality axioms

ClassicalDedekindReals.sig_not_dec :
  forall P : Prop, {~ ~ P} + {~ P} 
ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
Axioms.prop_ext : ClassicalFacts.prop_extensionality
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type)
    (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : U -> Type) 
    (x : Q p) (h : p = p),
  x = eq_rect p Q x p h
Classical_Prop.classic : forall P : Prop, P \/ ~ P
Ensembles.Extensionality_Ensembles :
  forall (U : Type) (A B : Ensembles.Ensemble U),
  Ensembles.Same_set A B -> A = B

Part 2, axiomatization of a malloc/free system, for use when the g.c.
  needs to allocate a new generation from the operating system's virtual memory.

library.mem_mgr : SeparationLogic.globals -> mpred.mpred
library.malloc_token_valid_pointer :
  forall (cs : compspecs.compspecs) (sh : shares.share)
    (t : Ctypes.type) (p : Values.val),
  BinInt.Z.le (expr.sizeof t) BinNums.Z0 ->
  seplog.derives (library.malloc_token sh t p)
    (expr.valid_pointer p)
library.malloc_token_local_facts :
  forall (cs : compspecs.compspecs) (sh : shares.share)
    (t : Ctypes.type) (p : Values.val),
  seplog.derives (library.malloc_token sh t p)
    (seplog.prop
       (field_at.malloc_compatible (expr.sizeof t) p))
library.malloc_token :
  compspecs.compspecs ->
  shares.share -> Ctypes.type -> Values.val -> mpred.mpred

*)