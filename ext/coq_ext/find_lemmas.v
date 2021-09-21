Require Import VST.floyd.proofauto.
Require Import Coq.Classes.Equivalence.
Require Import CertiGraph.lib.List_ext.

Section FindLemmas.

Context {size : Z}.
Context {inf: Z}.
Context {Z_EqDec : EquivDec.EqDec Z eq}. 

(* Find and lemmas about it *)

Fixpoint find {A: Type} {EA: EquivDec.EqDec A eq} (l : list A) (n : A) (ans : Z) :=
  match l with
  | [] => ans
  | h :: t => if EA h n
              then ans
              else (find t n (1 + ans))
  end.

Lemma find_index_gen: forall (l: list Z) i ans,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) ans = i + ans.
Proof.
  intros. generalize dependent i.
  generalize dependent ans. induction l.
  1: intros; rewrite Zlength_nil in H; exfalso; lia.
  unfold find.
  intros.
  destruct (Z_EqDec a (Znth i (a :: l))).
  - rewrite <- e in H0. clear - H H0.
    destruct (Z.eq_dec 0 i). 1: lia.
    destruct H. assert (0 < i) by lia.
    exfalso. apply H0.
    unfold sublist. replace (i-0) with i by lia. simpl.
    replace (Z.to_nat i) with (Z.to_nat (Z.succ (i-1))) by rep_lia.
    rewrite Z2Nat.inj_succ by lia.
    rewrite firstn_cons. simpl; left; trivial.
  - destruct (Z.eq_dec 0 i).
    1: rewrite <- e in c; rewrite Znth_0_cons in c;
      exfalso.
    apply c. reflexivity.
    assert (0 <= i - 1 < Zlength l) by
        (rewrite Zlength_cons in H; rep_lia).
    assert (~ In (Znth (i - 1) l) (sublist 0 (i - 1) l)). {
      rewrite <- (Znth_pos_cons i l a) by lia.
      rewrite <- (sublist_1_cons l a i).
      intro. apply H0.
      apply (sublist_In 1 i).
      rewrite sublist_sublist0 by lia. assumption.
    }
    pose proof (IHl (1 + ans) (i - 1) H1 H2).
    replace (i - 1 + (1 + ans)) with (i + ans) in H3 by lia.
    replace (Znth i (a :: l)) with (Znth (i - 1) l).
    2: { symmetry. apply Znth_pos_cons; lia. }
    rewrite <- H3.
    unfold find. trivial.
Qed.

Lemma find_index: forall (l: list Z) i,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) 0 = i.
Proof.
  intros. replace i with (i + 0) at 2 by lia.
  apply find_index_gen; trivial.
Qed.

Lemma find_range_gen: forall (l: list Z) target ans,
    In target l ->
    0 <= ans ->
    ans <= find l target ans < Zlength l + ans.
Proof.
  intros. generalize dependent target.
  generalize dependent ans.
  induction l.
  1: intros; simpl; now rewrite Zlength_nil.
  intros. apply in_inv in H. destruct H.
  - subst a. unfold find.
    destruct (Z_EqDec target target). 
    rewrite Zlength_cons. split; rep_lia.
    exfalso. apply c. reflexivity. 
  - unfold find. destruct (Z_EqDec a target).
    1: rewrite Zlength_cons; split; rep_lia.
    assert (0 <= 1 + ans) by lia.
    pose proof (IHl (1+ans) H1 target H).
    clear -H2. unfold find in H2.
    rewrite Zlength_cons. rep_lia.
Qed.

Lemma find_range: forall l target,
    In target l ->
    0 <= find l target 0 < Zlength l.
Proof.
  intros. replace (Zlength l) with (Zlength l + 0) by lia.
  apply find_range_gen; trivial; lia.
Qed.

Lemma Znth_find_gen:
  forall (l: list Z) target ans,
    0 <= ans ->
    In target l ->
    Znth ((find l target ans)-ans) l = target.
Proof.
  intros. generalize dependent ans.
  induction l. 1: inversion H0.
  intros.
  destruct H0.
  - subst target. simpl.
    destruct (Z_EqDec a a).
    + replace (ans-ans) with 0 by lia.
      rewrite Znth_0_cons; auto.
    + exfalso; apply c; reflexivity.
  - specialize (IHl H0).
    simpl.
    destruct (Z_EqDec a target).
    + replace (ans-ans) with 0 by lia.
      rewrite Znth_0_cons; auto.
    + assert (0 <= 1 + ans) by lia.
      specialize (IHl (1+ans) H1).
      rewrite Znth_pos_cons.
      replace (1+ans) with (ans+1) in IHl at 2 by lia.
      rewrite Z.sub_add_distr in IHl.
      assumption.
      destruct (find_range_gen l target (1+ans) H0 H1) as [? _].
      lia.
Qed.

Lemma Znth_find:
  forall (l: list Z) target,
    In target l ->
    Znth (find l target 0) l = target.
Proof.
  intros.
  replace (find l target 0) with (find l target 0 - 0) by lia.
  apply Znth_find_gen; [lia | assumption].
Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
  intros. induction H0.
  simpl. auto. simpl. unfold Z.min at 1.
  destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
  intros. revert x; induction al; simpl; intros.
  apply Z.min_comm. rewrite <- Z.min_assoc. f_equal. apply IHal.
Qed.

Theorem fold_min_general:
  forall (al: list Z)(i: Z),
    In i (al) ->
    forall x, List.fold_right Z.min x al <= i.
Proof.
  induction al; intros. 1: inversion H.
  destruct H.
  1: subst a; simpl; apply Z.le_min_l.
  simpl. rewrite Z.le_min_r. apply IHal, H.
  Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
    In i (al) ->
    List.fold_right Z.min (hd 0 al) al <= i.
Proof. intros. apply fold_min_general, H. Qed.

Lemma min_not_in_prev i l :
  Znth i l < fold_right Z.min (Znth 0 l) (sublist 0 i l) ->
  ~ In (Znth i l) (sublist 0 i l).
Proof.
  intros. intro.
  pose proof (fold_min_general (sublist 0 i l) (Znth i l) H0(Znth 0 l)). lia.
Qed.

Lemma min_in_list : forall l1 l2 starter,
    incl l1 l2 ->
    In starter l2 ->
    In (fold_right Z.min starter l1) l2.
Proof.
  intros. induction l1; trivial. simpl.
  destruct (Z.min_dec a (fold_right Z.min starter l1));
    rewrite e; clear e.
  apply H, in_eq.
  apply IHl1, (incl_cons_inv H).
Qed.

Lemma Znth_0_hd:
  forall list, Zlength list > 0 -> Znth 0 list = hd 0 list.
Proof.
  intros. induction list; inversion H.
  rewrite Znth_0_cons. trivial.
Qed.

Lemma min_picks_first:
  forall num mono start,
    start <= mono ->
    fold_right Z.min start (repeat mono num) = start.
Proof.
  intros. induction num; trivial.
  simpl. rewrite IHnum. rewrite Z.min_r; lia.
Qed.

Lemma find_src: forall src,
    0 < inf ->
    0 <= src < size ->
    find (upd_Znth src (repeat inf (Z.to_nat size)) 0)
         (fold_right Z.min (hd 0 (upd_Znth src (repeat inf (Z.to_nat size)) 0))
                     (upd_Znth src (repeat inf (Z.to_nat size)) 0)) 0 = src.
Proof.
  intros.
  assert (Ha: 0 <= src < Zlength (repeat inf (Z.to_nat size))). {
    rewrite Zlength_repeat; lia.
  }

  remember (upd_Znth src (repeat inf (Z.to_nat size)) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength;
      rewrite Zlength_repeat; lia.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l.
    2: lia.
    2: rewrite Zlength_repeat; lia.
    rewrite sublist_repeat by lia.
    replace (src - 0) with (src) by lia.
    intro. apply repeat_spec in H1. lia.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2; auto.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_repeat; try lia.
    2: rewrite Zlength_repeat; lia.
    repeat rewrite Zlength_repeat by lia.
    replace (src - 0) with (src) by lia.
    rewrite <- Znth_0_hd.
    2: { rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_repeat; lia. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same.
      2: rewrite Zlength_repeat; lia.
      simpl. rewrite Z.min_l; trivial.
      rewrite min_picks_first; lia.
    + rewrite upd_Znth_diff;
        try rewrite Zlength_repeat; try lia.
      rewrite Znth_repeat_inrange by lia.
      simpl. rewrite Z.min_l.
      1,2: rewrite min_picks_first.
      all: try lia; compute; inversion 1.
Qed.

Lemma fold_min_in_list: forall l, Zlength l > 0 -> In (fold_right Z.min (hd 0 l) l) l.
Proof.
  intros. apply min_in_list.
  - apply incl_refl.
  - rewrite <- Znth_0_hd by trivial. apply Znth_In; lia.
Qed.

Lemma find_app_In1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A) v ans, In v l1 -> find (l1++l2) v ans = find l1 v ans.
Proof.
induction l1; intros. contradiction.
destruct (EA v a). hnf in e. subst a.
simpl.
destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
destruct H. symmetry in H; contradiction.
simpl. destruct (EA a v). symmetry in e; contradiction.
rewrite IHl1; auto.
Qed.

Lemma find_accum_add1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans1 ans2, find l v (ans1+ans2) = ans1 + find l v ans2.
Proof.
induction l; intros.
simpl. auto.
simpl. destruct (EA a v). auto.
replace (1+(ans1+ans2)) with (ans1 + (1+ans2)) by lia. apply IHl.
Qed.

Lemma find_app_notIn1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, ~ In v l1 -> find (l1++l2) v ans = Zlength l1 + find l2 v ans.
Proof.
induction l1; intros. rewrite app_nil_l, Zlength_nil. lia.
assert (~ In v l1). unfold not; intros; apply H. right; auto.
simpl. destruct (EA a v). hnf in e; subst a. exfalso. apply H. left; auto.
rewrite Zlength_cons. rewrite IHl1; auto.
rewrite <- Z.add_1_r, <- Z.add_assoc. rewrite find_accum_add1. auto.
Qed.

Corollary find_notIn:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ~ In v l -> find l v ans = Zlength l + ans.
Proof.
intros. replace l with (l++nil). rewrite find_app_notIn1. simpl.
rewrite app_nil_r; auto.
auto. apply app_nil_r.
Qed.

Corollary find_notIn_0:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v, ~ In v l -> find l v 0 = Zlength l.
Proof. intros. rewrite find_notIn by auto. rewrite Z.add_0_r; auto. Qed.

Lemma find_In_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, In v l -> find l v ans < Zlength l + ans.
Proof.
induction l; intros. contradiction.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
assert (find l v ans < Zlength l + ans). apply IHl. destruct H. contradiction. auto.
lia.
Qed.

Lemma find_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find l v ans <= Zlength l + ans.
Proof.
induction l; intros. rewrite Zlength_nil; simpl; lia.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
specialize IHl with v ans.
lia.
Qed.

Lemma find_cons:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find (v::l) v ans = ans.
Proof.
intros. simpl. destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
Qed.

Lemma find_lbound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ans <= find l v ans.
Proof.
induction l; intros. simpl. lia.
simpl. destruct (EA a v). lia.
rewrite find_accum_add1. specialize IHl with v ans; lia.
Qed.

Lemma find_app_le:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, find l1 v ans <= find (l1++l2) v ans.
Proof.
induction l1; intros.
rewrite app_nil_l. simpl. apply find_lbound.
simpl. destruct (EA a v). lia.
do 2 rewrite find_accum_add1. specialize IHl1 with l2 v ans. lia.
Qed.

Lemma find_eq:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) x y acc, NoDup l -> In x l -> In y l -> find l x acc = find l y acc -> x = y.
Proof.
induction l; intros. contradiction.
destruct H0; destruct H1.
++
subst x; subst y. auto.
++
subst x. rewrite find_cons in H2.
simpl in H2. destruct (EA a y). hnf in e; subst y. trivial.
rewrite find_accum_add1 in H2. pose proof (find_lbound l y acc). lia.
++
subst y. rewrite find_cons in H2.
simpl in H2. destruct (EA a x). hnf in e; subst x. trivial.
rewrite find_accum_add1 in H2. pose proof (find_lbound l x acc). lia.
++
simpl in H2. destruct (EA a x). hnf in e; subst x. apply NoDup_cons_2 in H; contradiction.
destruct (EA a y). hnf in e; subst y. apply NoDup_cons_2 in H; contradiction.
do 2 rewrite find_accum_add1 in H2. apply (IHl x y acc).
apply NoDup_cons_1 in H; auto. auto. auto. lia.
Qed.

(***************FIND LEMMAS*******)

Context {E: Type}.
Context {E_EqDec: EquivDec.EqDec E eq}.

Lemma NoDup_incl_ordered_powerlist:
  forall (l: list E), NoDup l -> exists L,
  (forall l', (NoDup l' /\ incl l' l /\ (forall x y, In x l' -> In y l' -> (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0)))
  <-> In l' L).
Proof.
induction l; intros.
exists (nil::nil). intros; split; intros. destruct H0 as [? [? ?]]. destruct l'. left; auto.
assert (In e (e::l')). left; auto. apply H1 in H3; contradiction.
destruct H0. subst l'. split. apply NoDup_nil. split. unfold incl; intros; auto.
intros. simpl. lia.
contradiction.
(*inductive step*)
assert (~ In a l). apply NoDup_cons_2 in H; auto. apply NoDup_cons_1 in H.
destruct (IHl H) as [L ?]. clear IHl.
assert (forall l', In l' L -> ~ In a l').
intros. apply H1 in H2. destruct H2 as [? [? ?]]. unfold not; intros. apply H3 in H5. contradiction.
exists (L ++ map (fun l' => (a::l')) L).
intros; split; intros.
**
destruct H3 as [? [? ?]]. apply in_or_app.
destruct (in_dec E_EqDec a l').
****
right.
(*then l' must be of form (a::l'')*)
destruct l'. contradiction.
destruct (E_EqDec e a).
******
hnf in e0. subst e.
apply in_map. apply H1.
split. apply NoDup_cons_1 in H3; auto.
split. unfold incl; intros. assert (In a0 (a::l)). apply H4. right; auto.
destruct H7. subst a0. apply NoDup_cons_2 in H3. contradiction. auto.
intros.
assert (find (a :: l') x 0 <= find (a :: l') y 0 <-> find (a :: l) x 0 <= find (a :: l) y 0). apply H5.
right; auto. right; auto.
apply NoDup_cons_2 in H3.
simpl in H8.
destruct (E_EqDec a x). hnf in e. subst x. contradiction.
destruct (E_EqDec a y). hnf in e. subst y. contradiction.
replace 1 with (1+0) in H8 by lia. repeat rewrite find_accum_add1 in H8.
split; intros. lia. lia.
******
unfold complement, equiv in c.
assert (find (e :: l') e 0 <= find (e :: l') a 0 <-> find (a :: l) e 0 <= find (a :: l) a 0). apply H5.
left; auto. auto. simpl in H6.
destruct (E_EqDec e e). 2: { unfold complement, equiv in c0; contradiction. }
destruct (E_EqDec a a). 2: { unfold complement, equiv in c0; contradiction. }
clear e0 e1.
destruct (E_EqDec e a). hnf in e0; contradiction.
destruct (E_EqDec a e). hnf in e0; symmetry in e0; contradiction.
clear c0 c1.
assert (0 <= find l' a 1). { apply (Z.le_trans 0 1). lia. apply find_lbound. }
apply H6 in H7. assert (1 <= 0). { apply (Z.le_trans 1 (find l e 1)). apply find_lbound. auto. }
lia.
****
left. apply H1. split. auto. split. unfold incl; intros. assert (In a0 (a::l)). apply H4; auto.
destruct H7. subst a0. contradiction. auto.
intros. assert (find l' x 0 <= find l' y 0 <-> find (a :: l) x 0 <= find (a :: l) y 0). apply H5; auto.
simpl in H8. destruct (E_EqDec a x). hnf in e. subst x. contradiction.
destruct (E_EqDec a y). hnf in e. subst y. contradiction.
replace 1 with (1+0) in H8 by lia. do 2 rewrite find_accum_add1 in H8.
split; intros. apply H8 in H9. lia.
apply H8. lia.
**
apply in_app_or in H3. destruct H3.
****
apply H1 in H3. destruct H3 as [? [? ?]].
split. auto. split. unfold incl; intros. right. apply H4. auto.
intros.
assert (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0). apply H5; auto.
simpl.
destruct (E_EqDec a x). hnf in e; subst x. apply H4 in H6; contradiction.
destruct (E_EqDec a y). hnf in e; subst y. apply H4 in H7; contradiction.
replace 1 with (1+0) by lia. do 2 rewrite (find_accum_add1).
split; intros. apply H8 in H9. lia. lia.
****
apply list_in_map_inv in H3. destruct H3 as [lx [? ?]]. subst l'. rename lx into l'.
assert (~ In a l'). apply H2; auto. apply H1 in H4. destruct H4 as [? [? ?]].
split. apply NoDup_cons; auto.
split. unfold incl; intros. destruct H7. subst a0. left; auto.
right. apply H5. auto.
intros. destruct H7.
subst x. simpl. destruct (E_EqDec a a). 2: { unfold complement, equiv in c; contradiction. }
destruct (E_EqDec a y). lia. split; intros. apply (Z.le_trans 0 1). lia. apply find_lbound. apply (Z.le_trans 0 1). lia. apply find_lbound.
destruct H8. subst y. simpl.
destruct (E_EqDec a a). 2: { unfold complement, equiv in c; contradiction. }
destruct (E_EqDec a x). lia. split; intros.
assert (1 <= 0). apply (Z.le_trans 1 (find l' x 1)). apply find_lbound. lia. lia.
assert (1 <= 0). apply (Z.le_trans 1 (find l x 1)). apply find_lbound. lia. lia.
assert (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0). apply H6; auto. simpl.
destruct (E_EqDec a x). hnf in e; subst x; contradiction.
destruct (E_EqDec a y). hnf in e; subst y; contradiction.
replace 1 with (1+0) by lia. repeat rewrite find_accum_add1.
split; intros; lia.
Qed.

Lemma test2:
forall (l' l: list E), NoDup l -> NoDup l' -> incl l' l -> exists lsorted, Permutation lsorted l' /\
(forall a b, In a lsorted -> In b lsorted -> (find lsorted a 0 <= find lsorted b 0 <-> find l a 0 <= find l b 0)).
Proof.
induction l'; intros l Hl; intros.
exists nil. split. apply perm_nil. intros. contradiction.
assert (exists lsorted : list E,
         Permutation lsorted l' /\
         (forall a b : E, In a lsorted -> In b lsorted -> find lsorted a 0 <= find lsorted b 0 <-> find l a 0 <= find l b 0)).
apply IHl'. auto. apply NoDup_cons_1 in H; auto. unfold incl; intros. apply H0. right; auto. clear IHl'.
destruct H1 as [lsorted [? ?]].
assert (Ha: ~ In a lsorted). unfold not; intros. apply (Permutation_in (l':=l')) in H3. 2: auto.
apply NoDup_cons_2 in H; contradiction.
assert (Hsorted_NoDup: NoDup lsorted). apply (Permutation_NoDup (l:=l')). apply Permutation_sym; auto. apply NoDup_cons_1 in H; auto.
(*split the list*)
set (k:= find l a 0) in *.
assert (exists l1 l2, lsorted = l1++l2 /\ (forall x, In x l1 -> find l x 0 < find l a 0) /\ (forall x, In x l2 -> find l a 0 <= find l x 0)). {
clear H1.
induction lsorted. exists nil; exists nil. split. rewrite app_nil_r; auto.
split; intros; contradiction.
destruct (Z.lt_ge_cases (find l a0 0) (find l a 0)); rename H1 into Ha0.
++
assert (exists l1 l2 : list E,
              lsorted = l1 ++ l2 /\
              (forall x : E, In x l1 -> find l x 0 < find l a 0) /\ (forall x : E, In x l2 -> find l a 0 <= find l x 0)). {
apply IHlsorted. 2: { unfold not; intros. apply Ha. right; auto. }
2: { apply NoDup_cons_1 in Hsorted_NoDup; auto. }
intros. split; intros.
apply H2. right; auto. right; auto.
apply NoDup_cons_2 in Hsorted_NoDup.
simpl. destruct (E_EqDec a0 a1). hnf in e; subst a0; contradiction.
destruct (E_EqDec a0 b). hnf in e; subst a0; contradiction.
replace 1 with (1+0) by lia. do 2 rewrite find_accum_add1. lia.
apply H2 in H4. 2: right; auto. 2: right; auto.
simpl in H4. apply NoDup_cons_2 in Hsorted_NoDup.
destruct (E_EqDec a0 a1). hnf in e; subst a0; contradiction.
destruct (E_EqDec a0 b). hnf in e; subst a0; contradiction.
replace 1 with (1+0) in H4 by lia. do 2 rewrite find_accum_add1 in H4. lia.
} clear IHlsorted.
destruct H1 as [l1 [l2 [? [? ?]]]].
exists (a0::l1). exists l2. split. simpl. rewrite H1; auto.
split; intros. destruct H5. subst x; auto. apply H3; auto.
apply H4; auto.
++
exists nil. exists (a0::lsorted). split. auto.
split; intros. contradiction.
destruct H1. subst x. auto.
apply (Z.le_trans _ (find l a0 0)). auto.
apply H2. left; auto. right; auto.
rewrite find_cons. apply find_lbound.
}
destruct H3 as [l1 [l2 [? [? ?]]]]. subst lsorted.
exists (l1++a::l2).
split. { apply NoDup_Permutation. apply NoDup_app_inv. apply NoDup_app_l in Hsorted_NoDup; auto.
apply NoDup_cons. unfold not; intros; apply Ha. apply in_or_app; right; auto.
apply NoDup_app_r in Hsorted_NoDup; auto.
unfold not; intros. destruct H6. subst x. apply Ha. apply in_or_app; left; auto.
assert (~ In x l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
auto.
split; intros. apply in_app_or in H3; destruct H3. right. apply (Permutation_in (l:=l1++l2)); auto. apply in_or_app; left; auto.
destruct H3. subst x. left; auto. right. apply (Permutation_in (l:=l1++l2)); auto. apply in_or_app; right; auto.
apply in_or_app. destruct H3. subst x. right; left; auto.
apply (Permutation_in (l':=l1++l2)) in H3. 2: apply Permutation_sym; auto.
apply in_app_or in H3; destruct H3. left; auto. right; right; auto.
}
intros. apply in_app_or in H3. apply in_app_or in H6. specialize H2 with a0 b.
destruct H3; destruct H6.
**
rewrite (find_app_In1 l1 (a::l2)) by auto. rewrite find_app_In1 by auto.
rewrite find_app_In1 in H2 by auto. rewrite find_app_In1 in H2 by auto.
apply H2. apply in_or_app. left; auto. apply in_or_app; left; auto.
**
rewrite find_app_In1 by auto.
assert (~ In b l1). unfold not; intros. destruct H6. subst b. apply Ha. apply in_or_app; left; auto.
assert (~ In b l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
rewrite find_app_notIn1 by auto.
destruct H6. subst b. split; intros. apply Z.le_lteq. left; apply H4; auto.
apply (Z.le_trans _ (Zlength l1 + 0)). apply find_ubound. pose proof (find_lbound (a::l2) a 0); lia.
split; intros. apply (Z.le_trans _ (find l a 0)). apply Z.le_lteq. left; apply H4; auto. apply H5; auto.
apply (Z.le_trans _ (Zlength l1 + 0)). apply find_ubound. pose proof (find_lbound (a::l2) b 0); lia.
**
assert (~ In a0 l1). unfold not; intros. destruct H3. subst a0. apply Ha. apply in_or_app; left; auto.
assert (~ In a0 l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
(*this is false*)
rewrite find_app_notIn1 by auto. rewrite find_app_In1 by auto.
split; intros. assert (find l1 b 0 < Zlength l1 + 0). apply find_In_ubound; auto. rewrite Z.add_0_r in H9.
assert (0 <= find (a::l2) a0 0). apply find_lbound. lia.
destruct H3. subst a0.
****
assert (find l b 0 < find l a 0). apply H4; auto. lia.
****
assert (find l b 0 < find l a0 0). apply (Z.lt_le_trans _ (find l a 0)). apply H4; auto. apply H5; auto. lia.
**
assert (~ In a0 l1). unfold not; intros. destruct H3. subst a0. apply Ha. apply in_or_app; left; auto.
assert (~ In a0 l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
assert (~ In b l1). unfold not; intros. destruct H6. subst b. apply Ha. apply in_or_app; left; auto.
assert (~ In b l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
rewrite find_app_notIn1 by auto. rewrite find_app_notIn1 by auto.
rewrite find_app_notIn1 in H2 by auto. rewrite find_app_notIn1 in H2 by auto.
destruct H3; destruct H6.
****
subst a0. subst b. split; intros; lia.
****
subst a0. rewrite find_cons. split; intros. apply H5; auto. pose proof (find_lbound (a::l2) b 0); lia.
****
subst b. rewrite find_cons. (*falseness*)
split; intros.
assert (0 < find (a::l2) a0 0). simpl. destruct (E_EqDec a a0).
hnf in e. subst a0. exfalso; apply Ha. apply in_or_app; right; auto.
pose proof (find_lbound l2 a0 1). lia.
lia.
apply Z.le_lteq in H6. destruct H6.
assert (find l a 0 <= find l a0 0). apply H5; auto. lia.
assert (incl l' l). unfold incl; intros. apply H0. right; auto.
apply (find_eq l a0 a 0) in H6. subst a0. rewrite find_cons; lia.
auto. apply H9. apply (Permutation_in (l:= (l1++l2))); auto. apply in_or_app; right; auto.
apply H0. left; auto.
**** rewrite <- H2.
2: apply in_or_app; right; auto. 2: apply in_or_app; right; auto.
simpl.
destruct (E_EqDec a a0). hnf in e; subst a0. exfalso; apply Ha. apply in_or_app; right; auto.
destruct (E_EqDec a b). hnf in e; subst b. exfalso; apply Ha. apply in_or_app; right; auto.
replace 1 with (1+0) by lia. do 2 rewrite find_accum_add1. split; intros; lia.
Qed.

End FindLemmas.
