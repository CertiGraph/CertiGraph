Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import RamifyCoq.Coqlib.
Require Import VST.floyd.proofauto.
Require Import RamifyCoq.floyd_ext.semax_ram_lemmas.
Require Import RamifyCoq.floyd_ext.exists_trick.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
Require Import RamifyCoq.floyd_ext.comparable.

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

Ltac solve_split_by_closed :=
  repeat first
    [ apply split_by_closed_nil
    | apply split_by_closed_cons_closed; solve [repeat constructor; auto with closed]
    | apply split_by_closed_cons_unclosed].

Ltac localize P :=
  match goal with
  | |- semax ?Delta ?Pre ?c ?Post =>
         change (semax Delta Pre c Post) with (semax_ram Delta nil Pre c Post);
         abbreviate_RamFrame
  | |- semax_ram ?Delta _ ?Pre ?c ?Post => idtac
  end;
  match goal with
  | RamFrame := @abbreviate (list SingleFrame) ?F |-
    semax_ram ?Delta _ ?Pre ?c ?Post =>
         apply semax_ram_localize with P; eexists;
         abbreviate_RamFrame
  end.

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

Lemma pointer_val_val_is_pointer_or_null: forall x,
  is_pointer_or_null (pointer_val_val x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Hint Resolve pointer_val_val_is_pointer_or_null.
