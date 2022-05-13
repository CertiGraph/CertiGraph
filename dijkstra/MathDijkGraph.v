Require Export VST.floyd.proofauto.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Require Import VST.msl.seplog.
Require Import VST.zlist.sublist.
Require Import compcert.lib.Integers.

Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.path_lemmas.
Require Export CertiGraph.graph.MathAdjMatGraph.

Require Import Coq.Classes.EquivDec.
Require Export CertiGraph.priq_malloc.priq_arr_utils.

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
      (@SoundAdjMat size inf _ _ g);
    
    veb:
      (* from the AdjMat soundness above we already know 
       e is representable, 
       but for Dijkstra we need a further constraint. 
       *)
      forall e,
        evalid g e ->
        0 <= elabel g e <= Int.max_signed / size;

    cts: (* cost_to_self *)
      forall v, vvalid g v -> elabel g (v, v) = 0;

    sfr: (* size is further restricted *)
      size * 4 <= Int.max_signed;
    (* sizeof tint = 4 *)
    
    ifr: (* inf is further restricted *)
      Int.max_signed / size < inf <= Int.max_signed - (Int.max_signed / size)
                                                        
    }.

  (* And here is the GeneralGraph that we will use *)
  Definition DijkGG := (GeneralGraph V E DV DE DG (fun g => SoundDijk g)).

  (* Some handy coercions: *)
  Definition DijkGG_DijkLG (g: DijkGG): DijkLG := lg_gg g.
  Coercion DijkGG_DijkLG: DijkGG >-> DijkLG.
  Identity Coercion DijkLG_AdjMatLG: DijkLG >-> AdjMatLG.
  Identity Coercion AdjMatLG_LabeledGraph: AdjMatLG >-> LabeledGraph.

  (* We can always drag out SoundAdjMat *)
  Definition DijkGG_SoundAdjMat (g: DijkGG) :=
    @basic g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  (* A DijkGG can be weakened into an AdjMatGG *)
  Definition DijkGG_AdjMatGG (g: DijkGG) : AdjMatGG :=
    Build_GeneralGraph DV DE DG SoundAdjMat g (DijkGG_SoundAdjMat g).

  Coercion DijkGG_AdjMatGG: DijkGG >-> AdjMatGG.

  (* Great! So now when we want to access an AdjMat
   plugin, we can simply use the AdjMat getter 
   and pass it a DijkGG. The coercion will be seamless. 
   *)

  (* For the two Dijkstra-specigic plugins, 
   we create getters: 
   *)
  Definition valid_edge_bounds (g: DijkGG) :=
    @veb g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition cost_to_self (g: DijkGG) :=
    @cts g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition size_further_restricted (g: DijkGG) :=
    @sfr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition inf_further_restricted (g: DijkGG) :=
    @ifr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Lemma inf_further_restricted':
    forall (g: DijkGG),
      0 < inf < Int.max_signed.
  Proof.
    intros.
    pose proof (inf_further_restricted g).
    pose proof (size_representable g).
    split.
    - apply Z.le_lt_trans with (m := Int.max_signed / size);
        [|lia].
      apply Z.div_pos; [|lia]. compute; inversion 1.
    - destruct H as [_ ?].
      apply Z.le_lt_trans
        with (m := Int.max_signed - Int.max_signed/size); trivial.
      assert (0 < Int.max_signed / size). {
        apply Z.div_str_pos; trivial.
      }
      lia.
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
      apply (@inf_representable _ _ _ _ g).
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
      split; trivial.
      1: apply Z.le_trans with (m := 0); trivial; rep_lia.
      apply Z.le_trans with (m := (Int.max_signed / size)); trivial.
      apply H.
      pose proof (size_representable g).
      apply div_pos_le; lia.
    - rewrite H0 in n.
      replace (elabel g e) with inf by trivial.
      pose proof (inf_representable g).
      split; [|lia].
      apply Z.le_trans with (m := 0); [|lia].
      compute; inversion 1.
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
    split.
    - apply edge_representable.
    - intro. simpl in H2. lia. 
  Qed.

End MathDijkGraph.
