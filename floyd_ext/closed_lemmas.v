Require Import VST.floyd.base.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.

Local Open Scope logic.

Lemma closed_wrt_wand: forall (S : ident -> Prop) (P Q : environ -> mpred),
       closed_wrt_vars S P ->
       closed_wrt_vars S Q -> closed_wrt_vars S (P -* Q).
Proof.
  intros; hnf in *; intros.
  simpl. f_equal; eauto.
Qed.

Lemma closed_wrtl_wand: forall (S : ident -> Prop) (P Q : environ -> mpred),
       closed_wrt_lvars S P ->
       closed_wrt_lvars S Q -> closed_wrt_lvars S (P -* Q).
Proof.
  intros; hnf in *; intros.
  simpl. f_equal; eauto.
Qed.

Hint Resolve closed_wrt_wand closed_wrtl_wand : closed.
