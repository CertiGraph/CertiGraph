Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import CertiGraph.dijkstra.matrix_read.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Existing Instance CompSpecs.


Section GetCell.
  
  Context {size : Z}.

  (* helpers begin -- skippable *)
  
  Fixpoint nat_inc_list (n: nat) : list Z :=
    match n with
    | O => nil
    | S n' => nat_inc_list n' ++ (Z.of_nat n' :: nil)
    end.
  
  Lemma nat_inc_list_length: forall n, length (nat_inc_list n) = n. Proof. induction n; simpl; auto. rewrite app_length. simpl. rewrite IHn. lia. Qed.
  
  Lemma nat_inc_list_Zlength:
    forall n, Zlength (nat_inc_list n) = Z.of_nat n.
  Proof.
    intros. now rewrite Zlength_correct, nat_inc_list_length. Qed.
  
  Lemma nat_inc_list_i: forall i n,
      0 <= i < Z.of_nat n ->
      Znth i (nat_inc_list n) = i.
  Proof.
    intros. generalize dependent i. induction n.
    1: intros; exfalso; destruct H; rewrite Nat2Z.inj_0 in H0; lia.
    intros. simpl. rewrite Nat2Z.inj_succ in H. destruct H.
    apply Zlt_succ_le in H0. apply Zle_lt_or_eq in H0. destruct H0.
    - rewrite app_Znth1. apply IHn. lia.
      now rewrite nat_inc_list_Zlength.
    - rewrite app_Znth2 by (rewrite nat_inc_list_Zlength; lia). 
      rewrite H0. rewrite nat_inc_list_Zlength. simpl. 
      replace (Z.of_nat n - Z.of_nat n) with 0 by lia.
      rewrite Znth_0_cons; trivial.
  Qed.

  (* helpers end *)


  
  (* spatial begins *)

  Definition list_address (cs: compspecs) a index : val :=
    offset_val (index * sizeof (tarray tint size)) a.
  
  Definition list_rep sh (cs: compspecs) l contents_mat index :=
    let mylist := (Znth index contents_mat) in
    data_at sh (tarray tint size)
            (map Vint (map Int.repr mylist))
            (list_address cs l index).
  
  Definition DijkGraph g sh cs g_ptr :=
    iter_sepcon (list_rep sh cs g_ptr g) (nat_inc_list (Z.to_nat size)).

  Lemma DijkGraph_unfold: forall sh (cs: compspecs) g g_ptr i,
      0 <= i < size ->
      Zlength g = size ->
      DijkGraph g sh cs g_ptr =
      sepcon (iter_sepcon (list_rep sh cs g_ptr g)
                          (sublist 0 i (nat_inc_list (Z.to_nat size))))
             (sepcon
                (list_rep sh cs g_ptr g i)
                (iter_sepcon (list_rep sh cs g_ptr g)
                             (sublist (i + 1) (Zlength g) (nat_inc_list (Z.to_nat size))))).
  Proof.
    intros. unfold DijkGraph.
    replace (nat_inc_list (Z.to_nat size)) with
        (sublist 0 size (nat_inc_list (Z.to_nat size))) at 1.
    2: rewrite sublist_same; trivial; rewrite nat_inc_list_Zlength; lia.
    rewrite (sublist_split 0 i size),
    (sublist_split i (i+1) size), (sublist_one i); try lia.
    2, 3, 4: rewrite nat_inc_list_Zlength; rewrite Z2Nat.id; lia.
    rewrite nat_inc_list_i.
    2: rewrite Z2Nat_id', Z.max_r; lia.
    repeat rewrite iter_sepcon_app.
    simpl. now rewrite sepcon_emp, H0.
  Qed.

  (* spatial ends *)



  (* proof begins *)
  
  Definition getCell_spec :=
    DECLARE _getCell
    WITH sh: share,
         g: list (list Z),
         graph_ptr: pointer_val,
         u: Z,
         i : Z
    PRE [tptr (tptr tint), tint, tint]
    PROP (0 <= i < size;
         0 <= u < size;
         Zlength g = size)
    PARAMS (pointer_val_val graph_ptr;
           Vint (Int.repr u);
           Vint (Int.repr i))
    GLOBALS ()
    SEP (DijkGraph g sh CompSpecs (pointer_val_val graph_ptr))
    POST [tint]
    PROP ()
    RETURN (Vint (Int.repr (Znth i (Znth u g)))) 
    SEP (DijkGraph g sh CompSpecs (pointer_val_val graph_ptr)).

  Definition Gprog : funspecs :=
    ltac:(with_library prog [getCell_spec]).

  Lemma body_getCell: semax_body Vprog Gprog f_getCell getCell_spec.
  Proof.
    start_function.
    rewrite (DijkGraph_unfold _ _ _ _ u); trivial.
    Intros.
    freeze FR := (iter_sepcon _ _) (iter_sepcon _ _).
    unfold list_rep.
    Fail forward.
    (* Okay fine, this is a hint *)
    
    assert_PROP (force_val
                   (sem_add_ptr_int
                      (tptr tint)
                      Signed
                      (pointer_val_val graph_ptr)
                    (Vint (Int.repr u))) =
                 field_address
                   (Tarray tint size noattr)
                   [ArraySubsc u]
                   (pointer_val_val graph_ptr)). {
      entailer!. simpl.
      rewrite field_address_offset.
      1: f_equal.
      admit. (* even if we admit this... *)
    }
    Fail forward. 
    (* Why is THIS the error message? 
       Where did Tint I32 Signed noattr come into play?
     *)

  (* I have tried the basic experiments in C:
     
     int getCell (int **graph, int u, int i) {
         int *row = graph[u]'
         return row[i];
         }

     but this also gave me the weird type mismatch that we see here
   *)
    

  (*
    When I had the matrix coming in as an argument like
    "int graph[size][size]",
    I was able to do it in one step. 

    forward gave me a similar hint, and I did the following:
   *)

  (*
    assert_PROP (force_val
                   (sem_add_ptr_int
                      tint
                      Signed
                      (force_val
                         (sem_add_ptr_int
                            (tarray tint size)
                            Signed
                            (pointer_val_val graph_ptr)
                            (Vint (Int.repr u))))
                      (Vint (Int.repr i))) =
                 field_address
                   (tarray tint size)
                   [ArraySubsc i]
                   (@list_address
                      CompSpecs
                      (pointer_val_val graph_ptr)
                      u)). {
      entailer!.
      clear (* some stuff *) 
        unfold list_address. simpl.
      rewrite field_address_offset.
      1: { rewrite offset_offset_val; simpl; f_equal.
           rewrite Z.add_0_l. f_equal. lia. }            
      destruct H24 as [? [? [? [? ?]]]]. 
      (* H24 was itself a field_compatible argument *)
      unfold field_compatible; split3; [| | split3]; simpl; auto.
    }
    *)
                             
  
Abort.


  
