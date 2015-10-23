Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import VST.floyd.base.
Require Import VST.floyd.canon.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.reptype_lemmas. (* Related things should be moved to other files. *)
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.local2ptree.
Require Import VST.floyd.call_lemmas.
Require Import VST.floyd.forward.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.ramification.
Require Import RamifyCoq.floyd_ext.semax_ram_lemmas.
Require Import RamifyCoq.floyd_ext.exists_trick.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
Require Import RamifyCoq.floyd_ext.comparable.

Local Open Scope logic.

Lemma PROPx_andp: forall P Q, PROPx P Q = PROPx P TT && Q.
Proof.
  intros.
  unfold PROPx.
  rewrite andp_TT.
  auto.
Qed.

Lemma LOCALx_andp: forall P Q, LOCALx P Q = LOCALx P TT && Q.
Proof.
  intros.
  unfold LOCALx.
  rewrite andp_TT.
  auto.
Qed.

Lemma SEPx_andp: forall P Q R, PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q TT) && SEPx R.
Proof.
  intros.
  unfold PROPx, LOCALx.
  rewrite andp_TT.
  rewrite andp_assoc.
  auto.
Qed.

Inductive split_by_closed:
 statement -> list (environ -> Prop) -> list (environ -> Prop) -> list (environ -> Prop) -> Prop :=
 | split_by_closed_nil: forall s, split_by_closed s nil nil nil
 | split_by_closed_cons_closed: forall s q Q Q1 Q2,
     closed_wrt_modvars s (local q) ->
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) (q :: Q1) Q2
 | split_by_closed_cons_unclosed: forall s q Q Q1 Q2,
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) Q1 (q :: Q2).

Lemma insert_local': forall Q1 Q R,
  local Q1 && (LOCALx Q R) = LOCALx (Q1 :: Q) R.
Proof.
intros. extensionality rho.
unfold LOCALx, local; super_unfold_lift. simpl.
apply pred_ext; autorewrite with gather_prop; normalize;
decompose [and] H; clear H.
Qed.

Lemma split_by_closed_spec: forall s Q Q1 Q2,
  split_by_closed s Q Q1 Q2 ->
  EnvironStable (vars_relation (modifiedvars s)) (LOCALx Q1 TT) /\
  LOCALx Q TT = LOCALx Q1 TT && LOCALx Q2 TT.
Proof.
  intros.
  split.
  + rewrite EnvironStable_var_relation_closed.
    induction H.
    - auto with closed.
    - rewrite <- insert_local'.
      auto with closed.
    - auto.
  + induction H.
    - apply add_andp; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite andp_assoc; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite <- !andp_assoc.
      rewrite (andp_comm (local q)); auto.
Qed.

Lemma corable_PROP: forall P, corable (PROPx P TT).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold PROPx.
  apply corable_andp; auto.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl; auto.
Qed.

Lemma corable_LOCAL: forall P, corable (LOCALx P TT).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold LOCALx.
  apply corable_andp; [| unfold TT; auto].
  unfold local, lift1.
  unfold_lift.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl.
  intros.
  auto.
Qed.

Lemma solve_LOCALx_entailer: forall {cs: compspecs} P Ptemp Pvar Q Qtemp Qvar,
  local2ptree P Ptemp Pvar nil nil ->
  local2ptree Q Qtemp Qvar nil nil ->
  Forall (check_one_var_spec' Pvar) (PTree.elements Qvar) ->
  Forall (check_one_temp_spec Ptemp) (PTree.elements Qtemp) ->
  LOCALx P TT |-- LOCALx Q TT.
Proof.
  intros.
  erewrite (local2ptree_soundness'' P) by eauto.
  erewrite (local2ptree_soundness'' Q) by eauto.
  unfold LOCALx, local, lift1; simpl; normalize; intros.
  eapply check_specs_lemma'; eauto.
Qed.

(*
Lemma canonical_ram_reduce00: forall (P0 Q0 P Q: env -> mpred),
  corable P0 ->
  corable Q0 ->
  (P0 --> Q0) && (P0 
*)
Lemma canonical_ram_reduce0: forall QG RG QL RL s QL' RL' QG' QG1' QG2' RG',
  split_by_closed s QG' QG1' QG2' ->
  LOCALx QG TT |-- LOCALx QL TT ->
  LOCALx QG TT |-- LOCALx QG1' TT ->
  LOCALx QL' TT |-- LOCALx QG2' TT ->
  SEPx RG |-- SEPx RL * ModBox s (SEPx RL' -* SEPx RG') ->
  PROPx nil (LOCALx QG (SEPx RG)) |--
  PROPx nil (LOCALx QL (SEPx RL)) *
    ModBox s (PROPx nil (LOCALx QL' (SEPx RL')) -* 
                PROPx nil (LOCALx QG' (SEPx RG'))).
Proof.
  intros.
  apply split_by_closed_spec in H.
  destruct H.
  rewrite !(PROPx_andp _ (LOCALx _ _)).
  rewrite !(LOCALx_andp _ (SEPx _)).
  rewrite H4; clear H4 QG'.

  rewrite corable_andp_sepcon1 by apply corable_PROP.
  apply andp_derives; auto.

  rewrite corable_andp_sepcon1 by apply corable_LOCAL.
  apply andp_right; [apply andp_left1; auto |].

  eapply sepcon_EnvironBox_weaken; [apply corable_andp_wand_corable_andp; try apply corable_PROP |].
  eapply sepcon_EnvironBox_weaken; [apply andp_right; [| apply derives_refl]; apply imp_andp_adjoint; apply andp_left2; auto |].

  rewrite andp_assoc.  
  eapply sepcon_EnvironBox_weaken; [apply wand_corable_andp; try apply corable_LOCAL |].
  rewrite (EnvironBox_andp _ (LOCALx QG1' TT)).
  rewrite (@EnvironStable_EnvironBox _ _ _ _ (vars_relation_Equivalence _) (LOCALx QG1' TT)) by auto.
  rewrite corable_sepcon_andp1 by apply corable_LOCAL.
  apply andp_derives; auto.

  eapply sepcon_EnvironBox_weaken; [apply corable_andp_wand_corable_andp; try apply corable_LOCAL |].
  eapply sepcon_EnvironBox_weaken; [apply andp_right; [| apply derives_refl]; apply imp_andp_adjoint; apply andp_left2; auto |].
  auto.
Qed.

Lemma canonical_ram_reduce1: forall lG lL lL' lG' s G L L' G',
  extract_trivial_liftx lG G ->
  extract_trivial_liftx lL L ->
  extract_trivial_liftx lL' L' ->
  extract_trivial_liftx lG' G' ->
  fold_right sepcon emp G |--
    fold_right sepcon emp L *
     (fold_right sepcon emp L' -* fold_right sepcon emp G') ->
  SEPx lG |-- SEPx lL * ModBox s (SEPx lL' -* SEPx lG').
Proof.
  intros.
  apply extract_trivial_liftx_e in H.
  apply extract_trivial_liftx_e in H0.
  apply extract_trivial_liftx_e in H1.
  apply extract_trivial_liftx_e in H2.
  subst.
  intro rho; unfold SEPx at 1 2; simpl.
  rewrite go_lower_ModBox.
  rewrite !fold_right_sepcon_liftx.
  replace
   (ALL  rho' : environ ,
      !!vars_relation (modifiedvars s) rho rho' -->
      (SEPx (map liftx L') rho' -* SEPx (map liftx G') rho')) with
   (ALL  rho' : environ ,
      !!vars_relation (modifiedvars s) rho rho' -->
      (fold_right sepcon emp L' -* fold_right sepcon emp G'))
  by (apply allp_congr; intro; unfold SEPx; simpl; rewrite !fold_right_sepcon_liftx; auto).
  eapply derives_trans; [| apply sepcon_derives; [apply derives_refl | apply allp_derives; intro; apply imp_right2; apply derives_refl]].
  erewrite (allp_forall _ _ rho) by (intros; simpl; reflexivity).
  auto.
Qed.

(*

Lemma canonical_ram_reduce0: forall PG QG RG PL QL RL s PL' QL' RL' PG' QG' QG1' QG2' RG',
  split_by_closed s QG' QG1' QG2' ->
  LOCALx QG TT |-- LOCALx QL TT ->
  LOCALx QG TT |-- LOCALx QG1' TT ->
  LOCALx QL' TT |-- LOCALx QG2' TT ->
  PROPx PG (LOCALx nil (SEPx RG)) |--
  PROPx PL (LOCALx nil (SEPx RL)) *
    ModBox s (PROPx PL' (LOCALx nil (SEPx RL')) -* 
                PROPx PG' (LOCALx nil (SEPx RG'))) ->
  PROPx PG (LOCALx QG (SEPx RG)) |--
  PROPx PL (LOCALx QL (SEPx RL)) *
    ModBox s (PROPx PL' (LOCALx QL' (SEPx RL')) -* 
                PROPx PG' (LOCALx QG' (SEPx RG'))).
*)

Lemma destruct_pointer_val_VP: forall x,
  pointer_val_val x <> nullval \/
  isptr (pointer_val_val x) ->
  isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  split; simpl; auto.
  exists b, i; auto.
Qed.

Lemma destruct_pointer_val_NP: forall x,
  pointer_val_val x = nullval \/
  ~ isptr (pointer_val_val x) ->
  x = NullPointer.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  inversion H; try tauto.
  inversion H0.
Qed.

Ltac destruct_pointer_val x :=
  first [
    let H := fresh "H" in
    assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i) by (apply (destruct_pointer_val_VP x); tauto);
    destruct H as [?H [?b [?i ?H]]]
  | assert (x = NullPointer) by (apply (destruct_pointer_val_NP x); tauto)].

Ltac ram_simplify_Delta :=
  match goal with
  | |- semax_ram ?D _ _ _ _ => simplify_Delta_at D
  | _ => idtac
  end.

Ltac clear_RamFrame_abbr :=
  repeat match goal with
             | H := @abbreviate (list SingleFrame) _ |- _ => 
                        unfold H, abbreviate; clear H 
             | H := _: @SingleFrame' _ _ _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.
  
Ltac abbreviate_RamFrame_rec F RamFrame :=
  match F with
  | nil => idtac
  | RAM_FRAME.Build_SingleFrame ?l ?g ?s ?f :: ?F_tail =>
      abbreviate_RamFrame_rec F_tail RamFrame;
      let RamFrame0 := fresh "RamFrame" in
      set (RamFrame0 := f) in RamFrame;
      try change @RAM_FRAME.SingleFrame' with @SingleFrame' in RamFrame0
  end.

Ltac abbreviate_RamFrame :=
  clear_RamFrame_abbr;
  match goal with
  | |- semax_ram _ ?F _ _ _ =>
         let RamFrame := fresh "RamFrame" in
         set (RamFrame := @abbreviate (list SingleFrame) F);
         replace F with RamFrame by reflexivity;
         abbreviate_RamFrame_rec F RamFrame
  end.

Ltac abbreviate_semax_ram :=
  match goal with
  | |- semax_ram _ _ _ _ _ =>
         ram_simplify_Delta; unfold_abbrev';
         match goal with |- semax_ram ?D _ _ ?C ?P => 
            abbreviate D : tycontext as Delta;
            abbreviate P : ret_assert as POSTCONDITION ;
            match C with
            | Ssequence ?C1 ?C2 =>
               (* use the next 3 lines instead of "abbreviate"
                  in case C1 contains an instance of C2 *)
                let MC := fresh "MORE_COMMANDS" in
                pose (MC := @abbreviate _ C2);
                change C with (Ssequence C1 MC);
                match C1 with
                | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                | _ => idtac
                end
            | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
            | _ => idtac
            end
        end
  end;
  abbreviate_RamFrame;
  clear_abbrevs;
  simpl typeof.

Ltac pose_PROPx P :=
  match P with
  | ?Pr :: ?P0 => first [assert Pr as _ by assumption | assert Pr; [auto |]];
                  [.. | pose_PROPx P0]
  | nil => idtac
  end.

Ltac simple_Forall_pTree_from_elements :=
  repeat first [apply Forall_cons; [reflexivity |] | apply Forall_nil].

Ltac solve_LOCALx_entailer_tac :=
  eapply solve_LOCALx_entailer; [prove_local2ptree | prove_local2ptree | simple_Forall_pTree_from_elements | simple_Forall_pTree_from_elements].

Ltac localize L :=
  match goal with
  | |- semax ?Delta ?Pre ?c ?Post =>
         change (semax Delta Pre c Post) with (semax_ram Delta nil Pre c Post);
         abbreviate_RamFrame
  | |- semax_ram ?Delta _ ?Pre ?c ?Post => idtac
  end;
  match L with
  | PROPx ?P (LOCALx ?Q (SEPx ?R)) =>
         match goal with
         | |- semax_ram _ _ (PROPx _ (LOCALx ?Q_Goal (SEPx _))) _ _ =>
                first [
                  assert (LOCALx Q_Goal TT |-- LOCALx Q TT) as _ by solve_LOCALx_entailer_tac |
                  pose proof I as WARNING___New_local_part_should_be_a_subset_of_the_original_one]
         end;
         pose_PROPx P; [.. |
         apply semax_ram_localize with (PROPx nil (LOCALx Q (SEPx R))); eexists;
         abbreviate_RamFrame]
  end.

Ltac solve_split_by_closed :=
  repeat first
    [ apply split_by_closed_nil
    | apply split_by_closed_cons_closed; solve [repeat constructor; auto with closed]
    | apply split_by_closed_cons_unclosed].

(*
Ltac unlocalize Pre' :=
  match goal with
  | RamFrame := @abbreviate _ (RAM_FRAME.Build_SingleFrame ?l ?g ?s _ :: ?F) |-
    semax_ram ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c ?Ret =>
    clear_RamFrame_abbr;
    match Pre' with
    | PROPx ?P' (LOCALx ?Q' (SEPx ?R')) =>
        eapply (fun Q1' Q2' => semax_ram_unlocalize_PROP_LOCAL_SEP Delta l g s F P Q R c Ret P' Q' Q1' Q2' R'); gather_current_goal_with_evar
    end
  end.
*)
Lemma pointer_val_val_is_pointer_or_null: forall x,
  is_pointer_or_null (pointer_val_val x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Hint Resolve pointer_val_val_is_pointer_or_null.
