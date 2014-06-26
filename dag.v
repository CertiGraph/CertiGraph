Require Import msl.msl_classical.
Require Import msl.corec.
Require Import overlapping.
Require Import heap_model.

Local Open Scope pred.

Definition dagnode x d l r :=
  (mapsto x d) * (mapsto (x+1) l) * (mapsto (x+2) r).

Definition dagfun (Q: adr -> pred world) (x: adr) :=
  (!!(x = 0) && emp) ||
  (EX d:adr, EX l:adr, EX r:adr, dagnode x d l r * ((|> Q l) ⊗ (|> Q r))).
                                                                                                        
Lemma dagfun_HOcontractive : HOcontractive dagfun.
Proof.
  apply prove_HOcontractive. intros.
  unfold dagfun.
  apply subp_orp. apply subp_refl.
  apply subp_exp. intro d. apply subp_exp. intro l. apply subp_exp. intro r.
  apply subp_sepcon. apply subp_refl.
  apply subp_ocon; apply eqp_subp; eapply allp_left; eauto.
Qed.
Definition dag := HORec dagfun.

Lemma dag_unfold:
  forall x,
    dag x = (!!(x = 0) && emp) ||
            (EX d:adr, EX l:adr, EX r:adr, dagnode x d l r * ((|> dag l) ⊗ (|> dag r))).
Proof.
  intros. unfold dag at 1. rewrite HORec_fold_unfold. trivial. apply dagfun_HOcontractive.
Qed.
