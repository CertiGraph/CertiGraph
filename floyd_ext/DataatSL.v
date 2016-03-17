Require Import VST.floyd.base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import RamifyCoq.veric_ext.seplog.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.MapstoSL.

Local Open Scope logic.

Section DataAtMSL.

Context {cs: compspecs}.

Lemma exp_data_at_precise: forall sh t p,
  precise (EX v: reptype t, data_at sh t v p).
Proof.
  intros.
  apply derives_precise with (memory_block sh (sizeof t) p).
  + apply exp_left; intro v.
    apply data_at_memory_block; auto.
  + apply seplog.memory_block_precise.
Qed.

Lemma disj_data_at: forall sh t1 t2 p1 p2,
  sepalg.nonunit sh ->
  ~ pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
  disjointed (EX v: reptype t1, data_at sh t1 v p1) (EX v: reptype t2, data_at sh t2 v p2).
Proof.
  intros.
  eapply disj_derives; [| | apply disj_memory_block].
  + apply exp_left; intro v.
    apply data_at_memory_block.
  + apply exp_left; intro v.
    apply data_at_memory_block.
  + auto.
Qed.

Lemma data_at_conflict: forall sh t1 t2 p1 p2 v1 v2,
  sepalg.nonunit sh ->
  pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
  data_at sh t1 v1 p1 * data_at sh t2 v2 p2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [apply sepcon_derives; apply data_at_memory_block |].
  apply mapsto_memory_block.memory_block_overlap; auto.
Qed.

End DataAtMSL.
