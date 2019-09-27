Require Import VST.floyd.proofauto.
Require Import RamifyCoq.sample_mark.summatrix.
Require Import VST.msl.iter_sepcon.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition WORD_SIZE := 4.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Lemma sum_list_app:
  forall a b, sum_list (a++b) = sum_list a + sum_list b.
Proof. intros. induction a; simpl; omega. Qed.

(* Functional spec of this program *)
Definition sum_mat (m : list (list Z)) : Z := 
  sum_list (map sum_list m).

Lemma sum_mat_app:
  forall a b, sum_mat (a++b) =  sum_mat a + sum_mat b.
Proof.
  intros. induction a; unfold sum_mat in *; simpl; [|rewrite IHa]; omega.
Qed.

Fixpoint Z_inc_list (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => Z_inc_list n' ++ (Z.of_nat n' :: nil)
  end.

Lemma Z_inc_list_length: forall n, length (Z_inc_list n) = n.
Proof.
  intros. induction n. trivial.
  simpl. rewrite app_length. simpl. omega.
Qed.

Lemma Z_inc_list_in_iff: forall n v, List.In v (Z_inc_list n) <-> 0 <= v < Z.of_nat n.
Proof.
  induction n; intros; [simpl; intuition|]. rewrite Nat2Z.inj_succ. unfold Z.succ. simpl. rewrite in_app_iff.
  assert (0 <= v < Z.of_nat n + 1 <-> 0 <= v < Z.of_nat n \/ v = Z.of_nat n) by omega. rewrite H. clear H. rewrite IHn. simpl. intuition.
Qed.

Lemma Z_inc_list_eq : forall n len,
    (0 <= n < len)%nat ->
    Znth (Z.of_nat n) (Z_inc_list len) = Z.of_nat n.
Proof.
  intros. induction len. 1: exfalso; omega.
  simpl. admit.
  Admitted.

Definition list_address a index size : val :=
  offset_val (index * sizeof (tarray tuint size)) a.

Definition list_rep sh size l contents_mat index :=
  let mylist := (Znth index contents_mat) in
  data_at sh (tarray tuint size) (map Vint (map Int.repr mylist)) (list_address l index size).

Definition matrix_rep sh size contents_mat m : mpred :=
  iter_sepcon (list_rep sh size m contents_mat)
              (Z_inc_list (length contents_mat)).

Lemma matrix_rep_list_rep: forall sh i size ptr contents_mat,
    length contents_mat = Z.to_nat size ->
    (0 <= i < size)%Z ->
    matrix_rep sh size contents_mat ptr |--
    list_rep sh size ptr contents_mat i * TT.
Proof.
  intros. unfold matrix_rep. apply iter_sepcon_in_true.
  apply Z_inc_list_in_iff. rewrite H. rewrite Z2Nat.id; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition summatrix_spec : ident * funspec :=
 DECLARE _summatrix
         WITH a: val, sh : share, contents_mat : list (list Z)
  PRE [ _a OF (tptr (tarray tuint 2)), _n OF tint ]
  PROP  (readable_share sh; 
           Zlength contents_mat = 2;
           Forall (fun list => Zlength list = 2) contents_mat;
           Forall (fun list => Forall (fun x => 0 <= x <= Int.max_unsigned) list) contents_mat)
   LOCAL (temp _a a; temp _n (Vint (Int.repr 2)))
   SEP (matrix_rep sh 2 contents_mat a)
  POST [ tuint ]
   PROP ()
   LOCAL(temp ret_temp (Vint (Int.repr (sum_mat contents_mat))))
   SEP (matrix_rep sh 2 contents_mat a).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (1+2+3+4)))) 
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [summatrix_spec; main_spec]).

Lemma body_summatrix: semax_body Vprog Gprog f_summatrix summatrix_spec.
Proof.
  start_function. 
  forward.  (* i = 0; *)
  forward.  (* j = 0; *)
  forward.  (* s = 0; *)
  forward_while
    (EX i: Z,
     PROP  (0 <= i <= 2)
     LOCAL (temp _a a;
            temp _i (Vint (Int.repr i));
            (* temp _j (Vint (Int.repr j)); *)
            temp _n (Vint (Int.repr 2));
            temp _s (Vint (Int.repr (sum_mat (sublist 0 i contents_mat)))))
     SEP   (matrix_rep sh 2 contents_mat a)).
  * Exists 0; entailer!.  
  * entailer!.  
  * forward.
    forward_while
      (
       EX j: Z,
       PROP (0 <= j <= 2)
       LOCAL (temp _a a;            
              temp _i (Vint (Int.repr i));
              (* temp _a[_i] (list_address a i size); *)
              temp _j (Vint (Int.repr j));
              temp _n (Vint (Int.repr 2));
              temp _s
                   (Vint
                      (Int.add
                         (Int.repr (sum_list (sublist 0 j (Znth i contents_mat))))
                         (Int.repr (sum_mat (sublist 0 i contents_mat))))))
       SEP (matrix_rep sh 2 contents_mat a)).
  + Exists 0; entailer!.
  + entailer!.
  + assert_PROP (length contents_mat = Z.to_nat 2) by
        (entailer!; rewrite <- H; rewrite ZtoNat_Zlength; trivial).
    unfold matrix_rep.
    replace (Z_inc_list (Datatypes.length contents_mat)) with
        (sublist 0 (Zlength contents_mat) (Z_inc_list (Datatypes.length contents_mat))).
    2: { rewrite sublist_same; auto.
         repeat rewrite Zlength_correct; f_equal. 
         rewrite Z_inc_list_length. trivial. }
    rewrite H. rewrite (sublist_split 0 i 2).
    2: omega.
    2: { rewrite Zlength_correct. rewrite Z_inc_list_length.
         rewrite H4. rewrite Z2Nat.id; omega. }
    rewrite (sublist_split i (i+1) 2).
    2: omega.
    2: { rewrite Zlength_correct. rewrite Z_inc_list_length.
         rewrite H4. rewrite Z2Nat.id; omega. }
    repeat rewrite iter_sepcon_app.
    Intros.
    freeze F := (iter_sepcon (list_rep sh 2 a contents_mat)
            (sublist 0 i (Z_inc_list (Datatypes.length contents_mat)))) (iter_sepcon (list_rep sh 2 a contents_mat)
                                                                                     (sublist (i + 1) 2 (Z_inc_list (Datatypes.length contents_mat)))).
    rewrite (sublist_one i). simpl. Intros.
    replace (Znth i (Z_inc_list (Datatypes.length contents_mat))) with i.
    2: { admit. }


    (* *)
    (* sep_apply (matrix_rep_list_rep sh i 2 a contents_mat). 1: omega. *)
    unfold list_rep.
    (* Okay now I have a simple list-access problem.
     * I have the exact address (list_address) and I want the j'th item. 
     *)
    unfold list_address. simpl.
    (* At this point, other examples of reads just work.
     * They just do forward.
     * Refer to VST/progs/sumarray.v
     * The only difference I can see is that 
     *  "(offset_val (i * (4 * size)) a)"
     *  is not in LOCAL. "a" is. Should I fix that?? 
     *)
    Fail forward.
    (* Anyway I tried forward. It failed. So I started
     * doing what it hinted at... 
     *)
    assert_PROP (force_val
                   (sem_add_ptr_int tuint Signed
                                    (force_val (sem_add_ptr_int (tarray tuint 2) Signed a (Vint (Int.repr i))))
                                    (Vint (Int.repr j))) = field_address (tarray tuint 2) [ArraySubsc j] (list_address a i 2)).
    (* Btw, From vc.pdf I learnt that field_address actually needs 
     * the type of the array (tarray tuint 2), 
     * not the type of the j'th item. 
     * Okay cool, changed. Let's go.
     *)
    { entailer!. unfold list_address. simpl.
      rewrite field_address_offset.
      1: rewrite offset_offset_val; simpl; f_equal; rep_omega.
      unfold field_compatible in H5. destruct H5 as [? [? [? [? ?]]]].
      unfold field_compatible. split3; [| | split3]; auto.
      unfold legal_nested_field. split; [auto | simpl; omega].
    }
    (* I gave forward what it wanted. Let's go. *)
    assert (Zlength (Znth i contents_mat) = 2).
    { rewrite Forall_forall in H0. apply H0. apply Znth_In. omega. }
    forward. forward. forward.
    Exists (j+1). entailer!.
  - f_equal. f_equal.
    rewrite sublist_last_1; [|omega..].
    rewrite sum_list_app; simpl; omega.
  - unfold matrix_rep. (* Okay, need to go back and use a matrix unfold. *)
    thaw F.
    replace (Z_inc_list (Datatypes.length contents_mat)) with
        (sublist 0 (Zlength contents_mat) (Z_inc_list (Datatypes.length contents_mat))) at 3.
    2: { rewrite sublist_same; auto.
         repeat rewrite Zlength_correct; f_equal. 
         rewrite Z_inc_list_length. trivial. }
    rewrite H. rewrite (sublist_split 0 i 2).
    2: omega.
    2: { rewrite Zlength_correct. rewrite Z_inc_list_length.
         rewrite H4. rewrite Z2Nat.id; omega. }
    rewrite (sublist_split i (i+1) 2).
    2: omega.
    2: { rewrite Zlength_correct. rewrite Z_inc_list_length.
         rewrite H4. rewrite Z2Nat.id; omega. }
    repeat rewrite iter_sepcon_app.
    entailer!.
    rewrite (sublist_one i). simpl. Intros.
    replace (Znth i (Z_inc_list (Datatypes.length contents_mat))) with i.
    2: { admit. }
    entailer!.
    omega. admit. omega.

  - 
    omega.
  - admit.
  - omega.
    + forward. Exists (i+1).
      entailer!. assert (j = Zlength contents_mat) by omega.
      assert (j = 2) by omega.
      assert (Zlength (Znth i contents_mat) = 2).
      { rewrite Forall_forall in H0. apply H0. apply Znth_In. omega. }
      rewrite (sublist_same 0 j); trivial. 2: now rewrite H6.
      rewrite sublist_last_1; try rep_omega.
      rewrite sum_mat_app. do 2 f_equal.
      unfold sum_mat at 2.
      simpl. omega.
    * forward. entailer!.
      assert (i = Zlength contents_mat) by omega.
      rewrite sublist_same; trivial.
Admitted
