From klenee_complexity Require Import Endo Domain TM LFP Algebraic_Structures Terms.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Sets.Powerset Sets.Image.

Section Algebras.
    Context `{tm : TM}.

    Definition post_fn : Endo :=
      fun d => fun i => fun t' => exists t p, In _ (d i) t /\ t ○ p ⊢ t'.

    Lemma post_fn_monotone : Monotone post_fn.
    Proof.
      intros f g Hfg i t' Ht'.
      destruct Ht' as [t [p [Hin Htr]]].
      exists t, p; split; [ apply (Hfg i); exact Hin | exact Htr ].
    Qed.

    Lemma post_fn_continuous : Continuous post_fn.
    Proof.
      intros X. extensionality i.
      apply Extensionality_Ensembles; split; intros t' Ht'.
      - destruct Ht' as [t [p [[x [HX Hxin]] Htr]]].
        exists (post_fn x); split.
        + apply Im_def; exact HX.
        + exists t, p; split; [ exact Hxin | exact Htr ].
      - destruct Ht' as [d' [HIm Hd']].
        destruct HIm as [x HX y Hy]; subst y.
        destruct Hd' as [t [p [Hxin Htr]]].
        exists t, p; split; [ exists x; split; [ exact HX | exact Hxin ] | exact Htr ].
    Qed.

    Definition post : СontinuousEndo :=
      exist _ (exist _ post_fn post_fn_monotone) post_fn_continuous.

    Definition pre_fn : Endo :=
      fun d => fun i => fun t => exists t' p, In _ (d i) t' /\ t ○ p ⊢ t'.

    Lemma pre_fn_monotone : Monotone pre_fn.
    Proof.
      intros f g Hfg i t Ht.
      destruct Ht as [t' [p [Hin Htr]]].
      exists t', p; split; [ apply (Hfg i); exact Hin | exact Htr ].
    Qed.

    Lemma pre_fn_continuous : Continuous pre_fn.
    Proof.
      intros X. extensionality i.
      apply Extensionality_Ensembles; split; intros t Ht.
      - destruct Ht as [t' [p [[x [HX Hxin]] Htr]]].
        exists (pre_fn x); split.
        + apply Im_def; exact HX.
        + exists t', p; split; [ exact Hxin | exact Htr ].
      - destruct Ht as [d' [HIm Hd']].
        destruct HIm as [x HX y Hy]; subst y.
        destruct Hd' as [t' [p [Hxin Htr]]].
        exists t', p; split; [ exists x; split; [ exact HX | exact Hxin ] | exact Htr ].
    Qed.

    Definition pre : СontinuousEndo :=
      exist _ (exist _ pre_fn pre_fn_monotone) pre_fn_continuous.

    Definition dpre_fn : Endo :=
      fun d => fun i => fun t => forall t' p, t ○ p ⊢ t' -> In _ (d i) t'.

    Lemma dpre_fn_monotone : Monotone dpre_fn.
    Proof.
      intros f g Hfg i t Ht t' p Htr.
      exact (Hfg i t' (Ht t' p Htr)).
    Qed.

    Lemma dpre_fn_meet_continuous :
      forall X, dpre_fn (domain_glb X) = domain_glb (Im _ _ X dpre_fn).
    Proof.
      intros X. extensionality i.
      apply Extensionality_Ensembles; split; intros t Ht.
      - intros d' HIm; destruct HIm as [x HX y Hy]; subst y.
        intros t' p Htr. exact (Ht t' p Htr x HX).
      - intros t' p Htr x HX.
        assert (Hx : In _ (dpre_fn x i) t)
          by (apply (Ht (dpre_fn x)); apply Im_def; exact HX).
        exact (Hx t' p Htr).
    Qed.

    Definition dpre : MonotoneEndo := exist _ dpre_fn dpre_fn_monotone.

    Definition dpost_fn : Endo :=
      fun d => fun i => fun t' => forall t p, t ○ p ⊢ t' -> In _ (d i) t.

    Lemma dpost_fn_monotone : Monotone dpost_fn.
    Proof.
      intros f g Hfg i t' Ht' t p Htr.
      exact (Hfg i t (Ht' t p Htr)).
    Qed.

    Lemma dpost_fn_meet_continuous :
      forall X, dpost_fn (domain_glb X) = domain_glb (Im _ _ X dpost_fn).
    Proof.
      intros X. extensionality i.
      apply Extensionality_Ensembles; split; intros t' Ht'.
      - intros d' HIm; destruct HIm as [x HX y Hy]; subst y.
        intros t p Htr. exact (Ht' t p Htr x HX).
      - intros t p Htr x HX.
        assert (Hx : In _ (dpost_fn x i) t')
          by (apply (Ht' (dpost_fn x)); apply Im_def; exact HX).
        exact (Hx t p Htr).
    Qed.

    Definition dpost : MonotoneEndo := exist _ dpost_fn dpost_fn_monotone.

    Equations A_interp {X} (v : X -> MonotoneEndo) (t : @ATerm X) : MonotoneEndo := {
      A_interp v (letter a)  := v a;
      A_interp v zero        := 0;
      A_interp v one         := 1;
      A_interp v (plus a b)  := A_interp v a + A_interp v b;
      A_interp v (dot a b)   := A_interp v a * A_interp v b;
      A_interp v (star a)    := (A_interp v a) #;
      A_interp v (dual a)    := (A_interp v a) ~
    }.

    Lemma A_interp_sound {X} (v : X -> MonotoneEndo) :
      forall t1 t2, t1 == t2 -> A_interp v t1 = A_interp v t2.
    Proof.
      intros t1 t2 H; induction H; autorewrite with A_interp in *.
      all: try congruence.
      - apply plus_idem.
      - apply plus_com.
      - apply plus_assoc.
      - rewrite plus_com; apply plus_neutral_left.
      - apply dot_assoc.
      - apply dot_neutral_right.
      - apply dot_neutral_left.
      - apply dot_ann_left.
      - apply dot_distr_left.
      - symmetry; rewrite plus_com; apply star_make_right.
      - apply (proj1 (leq_plus_def _ _)); apply star_destruct_left;
          apply (proj2 (leq_plus_def _ _)); assumption.
      - apply dual_involutive.
      - apply (proj1 (leq_plus_def _ _)); apply (proj1 (dual_antitone _ _));
          apply (proj2 (leq_plus_def _ _)); assumption.
      - apply dual_dot.
      - apply dual_zero_law.
    Qed.

    Lemma A_interp_continuous {X} (v : X -> MonotoneEndo)
        (Hv : forall a, Continuous (me_fn (v a))) :
      forall t, NoDual t -> Continuous (me_fn (A_interp v t)).
    Proof.
      intros t H; induction H; autorewrite with A_interp.
      - apply Hv.
      - exact czero_continuous.
      - exact id_continuous.
      - apply cplus_continuous; assumption.
      - apply compose_continuous; assumption.
      - apply endo_star_continuous; (assumption || apply me_mono).
    Qed.

    Definition N_interp {X} (v : X -> MonotoneEndo)
        (Hv : forall a, Continuous (me_fn (v a))) (nt : @NTerm X) : СontinuousEndo :=
      exist _ (A_interp v (proj1_sig nt))
              (A_interp_continuous v Hv (proj1_sig nt) (proj2_sig nt)).

    Lemma N_interp_sound {X} (v : X -> MonotoneEndo)
        (Hv : forall a, Continuous (me_fn (v a))) :
      forall (t1 t2 : @NTerm X),
        proj1_sig t1 == proj1_sig t2 -> N_interp v Hv t1 = N_interp v Hv t2.
    Proof.
      intros [t1 H1] [t2 H2] Heq; unfold N_interp.
      apply sig_eq; simpl.
      now apply A_interp_sound.
    Qed.

End Algebras.
