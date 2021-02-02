Require Import CertiGraph.dijkstra.dijkstra_env.
Require Export CertiGraph.graph.MathAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section MathDijkGraph.

  Context {size : Z}.
  Context {inf : Z}.
  Context {V_EqDec : EqDec V eq}. 
  Context {E_EqDec : EqDec E eq}. 

  (* Here is the LabeledGraph *)
  Definition DijkLG := AdjMatLG.

  (* The soundness condition *)
  Class SoundDijk (g: DijkLG) :=
    {
    basic:
      (* first, we can take AdjMat's soundness wholesale *)
      @SoundAdjMat size inf g;
    
    veb:
      (* from the AdjMat soundness above we already know 
         e is representable, 
         but for Dijkstra we need a further constraint. 
       *)
      forall e,
        evalid g e ->
        0 <= elabel g e <= (Int.max_signed / size) - 1;

    cts: (* cost_to_self *)
      forall v, vvalid g v -> elabel g (v, v) = 0;

    sfr: (* size is further restricted *)
      size * 4 <= Int.max_signed;
    (* because sizeof tint = 4 *)
    
    ifr: (* inf is further restricted *)
      (Int.max_signed / size) - 1 < inf <= Int.max_signed - (Int.max_signed / size) + 1
                                                        
    }.

  (* And here is the GeneralGraph that we will use *)
  Definition DijkGG := (GeneralGraph V E DV DE DG (fun g => SoundDijk g)).

  (* Some handy coercions: *)
  Identity Coercion AdjMatLG_DijkLG: DijkLG >-> AdjMatLG.
  Identity Coercion LabeledGraph_AdjMatLG: AdjMatLG >-> LabeledGraph.

  (* We can drag out the soundness condition *)
  Definition SoundDijk_DijkGG (g: DijkGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

  (* We can always drag out SoundAdjMat *)
  Definition SoundAdjMat_DijkGG (g: DijkGG) :=
    @basic g (SoundDijk_DijkGG g).

  (* A DijkGG can be weakened into an AdjMatGG *)
  Definition AdjMatGG_DijkGG (g: DijkGG) : AdjMatGG :=
    Build_GeneralGraph DV DE DG SoundAdjMat g (SoundAdjMat_DijkGG g).

  Coercion AdjMatGG_DijkGG: DijkGG >-> AdjMatGG.

  (* Great! So now when we want to access an AdjMat
     plugin, we can simply use the AdjMat getter 
     and pass it a DijkGG. The coercion will be seamless. 
   *)

  (* For the four Dijkstra-specific plugins, we create getters: *)
  Definition valid_edge_bounds (g: DijkGG) :=
    @veb g (SoundDijk_DijkGG g).

  Definition cost_to_self (g: DijkGG) :=
    @cts g (SoundDijk_DijkGG g).

  Definition size_further_restricted (g: DijkGG) :=
    @sfr g (SoundDijk_DijkGG g).

  Definition inf_further_restricted (g: DijkGG) :=
    @ifr g (SoundDijk_DijkGG g).

  Lemma inf_bounds:
    forall (g: DijkGG),
      0 < inf < Int.max_signed.
  Proof.
    intros.
    apply (inf_representable g).
  Qed.

  (* And now some lemmas that come from soundness plugins. *)

  Lemma edge_cost_pos:
    forall (g: DijkGG) e,
      0 <= elabel g e.
  Proof.
    intros.
    pose proof (valid_edge_bounds g e).
    pose proof (invalid_edge_weight g e).
    destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
    - apply H; trivial.
    - rewrite H0 in n.
      replace (elabel g e) with inf by trivial.
      pose proof (@inf_representable _ _ g). lia.
  Qed.

  Lemma div_pos_le:
    forall a b,
      0 <= a ->
      0 < b ->
      a / b <= a.
  Proof.
    intros.
    rewrite <- (Z2Nat.id a); trivial.
    rewrite <- (Z2Nat.id b); [|lia].
    remember (Z.to_nat a) as n1.
    remember (Z.to_nat b) as n2.
    rewrite <- div_Zdiv by lia.
    apply inj_le.
    replace n1 with (Nat.div n1 1) at 2.
    2: apply Nat.div_1_r.
    apply Nat.div_le_compat_l.
    lia.
  Qed.

  Lemma edge_representable:
    forall (g: DijkGG) e,
      Int.min_signed <= elabel g e <= Int.max_signed.
  Proof.
    intros.
    pose proof (valid_edge_bounds g e).
    pose proof (invalid_edge_weight g e).
    pose proof (edge_cost_pos g e).
    destruct (@evalid_dec _ _ _ _ g (finGraph g) e).
    - specialize (H e0). 
      split; trivial. rep_lia.
      apply Z.le_trans with (m := (Int.max_signed / size) - 1); trivial.
      apply H.
      pose proof (size_representable g).
      apply Z.le_trans with (m := Int.max_signed / size).
      lia.
      apply div_pos_le; lia.
    - rewrite H0 in n.
      replace (elabel g e) with inf by trivial.
      pose proof (inf_representable g).
      split; rep_lia.
  Qed.

  Lemma strong_evalid_dijk:
    forall (g: DijkGG) a b,
      vvalid g a ->
      vvalid g b ->
      elabel g (a, b) < inf ->
      strong_evalid g (a,b).
  Proof.
    intros.
    split3;
      [rewrite (evalid_meaning g) |
       rewrite (edge_src_fst g) |
       rewrite (edge_dst_snd g)]; trivial.
    split; trivial.
    apply edge_representable.
  Qed.
  
End MathDijkGraph.
