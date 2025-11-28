From klenee_complexity Require Import Algebraic_Structures Domain Conf.
From Coq Require Import Program.Basics Strings.String.
From Coq Require Import Sets.Powerset Sets.Image.
From Coq Require Import Logic.FunctionalExtensionality.

Definition Endo := Domain -> Domain.

Axiom endo_monotone : forall (z : Endo) (f g : Domain),
    f <== g -> z f <== z g.

Definition СontinuousEndo := Endo.

Axiom endo_continuous : forall (a : СontinuousEndo) (X : Ensemble Domain),
    a (domain_lub X) = domain_lub (Im _ _ X a).

Lemma endo_continuous_binary : forall (a : СontinuousEndo) (x y : Domain),
    a (x + y) = a x + a y.
Proof.
  intros a x y.
  assert (H : x + y = domain_lub (Union _ (Singleton _ x) (Singleton _ y))).
  {
    rewrite domain_lub_union.
    rewrite domain_lub_singleton.
    rewrite domain_lub_singleton.
    reflexivity.
  }
  rewrite H.
  
  rewrite endo_continuous.
  
  assert (Im_eq : Im _ _ (Union _ (Singleton _ x) (Singleton _ y)) a = 
              Union _ (Singleton _ (a x)) (Singleton _ (a y))).
  {
    apply Extensionality_Ensembles.
    split.
    - intros z Hz.
      destruct Hz as [w Hw].
      destruct Hw as [w Hw|w Hw].
      + destruct Hw. left. red. rewrite <- H0.  constructor.
      + destruct Hw. right. red. rewrite <- H0. constructor.
    - intros z Hz.
      destruct Hz as [z Hz|z Hz].
      + destruct Hz. apply Im_intro with x.
        * left. constructor.
        * reflexivity.
      + destruct Hz. apply Im_intro with y.
        * right. constructor.
        * reflexivity.
  }
  rewrite Im_eq.
  
  rewrite domain_lub_union.
  rewrite domain_lub_singleton.
  rewrite domain_lub_singleton.
  reflexivity.
Qed.

Instance Endo_MonoidOps : Monoid_Ops Endo := {
    one := id;
    dot := compose; 
}.

Instance Endo_Monoid : Monoid (Mo := Endo_MonoidOps) := {
    dot_assoc := fun x y z => eq_refl;
    dot_neutral_left := fun x => eq_refl;
    dot_neutral_right := fun x => eq_refl;
}.

Instance Endo_SemiLatticeOps : SemiLattice_Ops Endo := {
  zero := fun _ => zero;
  plus a b := fun d => a d + b d;
}.

Instance Endo_LeqOp : Leq_Op Endo := {
    leq a b := a + b = b
}.

Lemma endo_leq_refl : forall (a : Endo), a <== a.
Proof.
  intro a.
  unfold leq, Endo_LeqOp; simpl.
  apply functional_extensionality.
  intro d.
  apply domain_plus_idem.
Qed.

Lemma endo_leq_antisym : forall (x y : Endo), 
    x <== y -> y <== x -> x = y.
Proof.
  unfold leq, Endo_LeqOp; simpl.
  intros x y Hxy Hyx.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  apply Extensionality_Ensembles.
  split.
  - intros t Ht.
    apply (f_equal (fun f => f d i)) in Hxy.
    simpl in Hxy.
    unfold plus, Endo_SemiLatticeOps in Hxy.
    simpl in Hxy.
    assert (H : In Trace (Union Trace (x d i) (y d i)) t).
    { apply Union_introl; assumption. }
    rewrite Hxy in H.
    assumption.
  - intros t Ht.
    apply (f_equal (fun f => f d i)) in Hyx.
    simpl in Hyx.
    unfold plus, Endo_SemiLatticeOps in Hyx.
    simpl in Hyx.
    assert (H : In Trace (Union Trace (y d i) (x d i)) t).
    { apply Union_introl; assumption. }
    rewrite Hyx in H.
    assumption.
Qed.

Lemma endo_leq_trans : forall (x y z : Endo), 
    x <== y -> y <== z -> x <== z.
Proof.
  unfold leq, Endo_LeqOp; simpl.
  intros x y z Hxy Hyz.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - intros t Ht.
    inversion Ht as [t' H1 | t' H2].
    + pose proof (f_equal (fun f => f d i) Hxy) as Hxy'.
      simpl in Hxy'.
      unfold plus, Endo_SemiLatticeOps in Hxy'.
      simpl in Hxy'.
      assert (Ht_y : In Trace (y d i) t).
      {
        rewrite <- Hxy'.
        apply Union_introl.
        assumption.
      }
      pose proof (f_equal (fun f => f d i) Hyz) as Hyz'.
      simpl in Hyz'.
      unfold plus, Endo_SemiLatticeOps in Hyz'.
      simpl in Hyz'.
      rewrite <- Hyz'.
      apply Union_introl.
      assumption.
    + assumption.
  - intros t Ht.
    apply Union_intror.
    assumption.
Qed.

Instance Endo_PartiallyOrdered : PartiallyOrdered (Lo := Endo_LeqOp) := {
  leq_refl := endo_leq_refl;
  leq_antisym := endo_leq_antisym;
  leq_trans := endo_leq_trans;
}.

Lemma endo_leq_plus_def : forall (x y : Endo), 
    x <== y <-> x + y = y.
Proof.
  intros x y.
  split.
  - intro H. exact H.
  - intro H. exact H.
Qed.

Lemma endo_plus_neutral_left : forall (x : Endo), 
    0 + x = x.
Proof.
  intros x.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  unfold plus, zero, Endo_SemiLatticeOps; simpl.
  unfold zero, Domain_SemiLatticeOps.
  apply Extensionality_Ensembles.
  split.
  - intros t H. inversion H; [inversion H0 | assumption].
  - intros t H. apply Union_intror; assumption.
Qed.

Lemma endo_plus_idem : forall (x : Endo), 
    x + x = x.
Proof.
  intros x.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  unfold plus, Endo_SemiLatticeOps; simpl.
  apply Extensionality_Ensembles.
  split.
  - intros t H. inversion H; assumption.
  - intros t H. apply Union_introl; assumption.
Qed.

Lemma endo_plus_assoc : forall (x y z : Endo), 
    x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  unfold plus, Endo_SemiLatticeOps; simpl.
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    inversion H as [t' H1 | t' H1].
    + apply Union_introl. apply Union_introl. assumption.
    + inversion H1 as [t'' H2 | t'' H2].
      * apply Union_introl. apply Union_intror. assumption.
      * apply Union_intror. assumption.
  - intros t H.
    inversion H as [t' H1 | t' H1].
    + inversion H1 as [t'' H2 | t'' H2].
      * apply Union_introl. assumption.
      * apply Union_intror. apply Union_introl. assumption.
    + apply Union_intror. apply Union_intror. assumption.
Qed.

Lemma endo_plus_com : forall (x y : Endo), 
    x + y = y + x.
Proof.
  intros x y.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  unfold plus, Endo_SemiLatticeOps; simpl.
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    inversion H; [apply Union_intror | apply Union_introl]; assumption.
  - intros t H.
    inversion H; [apply Union_intror | apply Union_introl]; assumption.
Qed.

Instance Endo_SemiLattice : SemiLattice (SLo := Endo_SemiLatticeOps) (Lo := Endo_LeqOp) := {
    PO_SemiLattice := Endo_PartiallyOrdered;
    leq_plus_def := endo_leq_plus_def;
    plus_neutral_left := endo_plus_neutral_left;
    plus_idem := endo_plus_idem;
    plus_assoc := endo_plus_assoc;
    plus_com := endo_plus_com
}.

Lemma endo_dot_ann_left : forall (x : Endo), 0 * x = 0.
Proof.
  intros x.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  unfold dot, zero, Endo_MonoidOps, Endo_SemiLatticeOps; simpl.
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    inversion H.
  - intros t H.
    inversion H.
Qed.

Lemma endo_dot_distr_left : forall (x y z : Endo), 
    (x + y) * z = x * z + y * z.
Proof.
  intros x y z.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  reflexivity.
Qed.

Lemma endo_comp_monotone : forall (z : Endo) (x y : Endo),
    x <== y -> z * x <== z * y.
Proof.
  intros z x y Hleq.
  apply functional_extensionality.
  intro d.
  apply functional_extensionality.
  intro i.
  
  assert (x_d_le_y_d : x d <== y d).
  {
    intro j.
    pose proof (f_equal (fun f => f d j) Hleq) as Heq.
    simpl in Heq.
    red; intros t Ht.
    rewrite <- Heq.
    apply Union_introl.
    assumption.
  }
  
  specialize (endo_monotone z (x d) (y d) x_d_le_y_d).
  intro Hz_mono.
  specialize (Hz_mono i).
  
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    inversion H as [t' H1 | t' H2].
    + apply Hz_mono.
      assumption.
    + assumption.
  - intros t H.
    apply Union_intror.
    assumption.
Qed.

Lemma plus_leq_upper_bound : forall (a b c : Endo),
  a <== c -> b <== c -> a + b <== c.
Proof.
  intros a b c Ha Hb.
  apply leq_plus_def.
  rewrite <- plus_assoc.
  rewrite Hb.
  rewrite Ha.
  reflexivity.
Qed.

Lemma endo_dot_distr_leq_right : forall (x y z : Endo),
    z * x + z * y <== z * (x + y).
Proof.
  intros x y z.
  
  assert (Hx : x <== x + y).
  {
    apply leq_plus_def.
    apply (eq_trans (plus_assoc x x y)).
    rewrite plus_idem.
    reflexivity. 
  }
  
  assert (Hy : y <== x + y).
  {
    apply leq_plus_def.
    apply (eq_trans (plus_assoc y x y)).
    rewrite <- plus_com.
    apply (eq_trans (plus_assoc y y x)).
    rewrite plus_idem.
    rewrite <- plus_com.
    reflexivity.
  }
  
  assert (Hzx : z * x <== z * (x + y)).
  { apply endo_comp_monotone. assumption. }
  
  assert (Hzy : z * y <== z * (x + y)).
  { apply endo_comp_monotone. assumption. }

  apply plus_leq_upper_bound.
  - exact Hzx.
  - exact Hzy.
Qed.

Instance Endo_LeftHandedIdemSemiRing : LeftHandedIdemSemiRing (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (Lo := Endo_LeqOp) := {
    LHISR_Monoid := Endo_Monoid;
    LHISR_SemiLattice := Endo_SemiLattice;
    dot_ann_left := endo_dot_ann_left;
    dot_distr_left := endo_dot_distr_left;
    dot_distr_leq_right := endo_dot_distr_leq_right
}.

Lemma endo_dot_distr_right : forall (z x y : СontinuousEndo), 
    z * (x + y) = z * x + z * y.
Proof.
  intros z x y.
  apply functional_extensionality.
  intro d.
  unfold dot, plus, Endo_MonoidOps, Endo_SemiLatticeOps; simpl.
  unfold compose.
  
  assert (H: (fun i : string => Union Trace (x d i) (y d i)) = plus (x d) (y d)).
  { apply functional_extensionality; intro i. reflexivity. }
  
  rewrite H.
  rewrite endo_continuous_binary.
  reflexivity.
Qed.

Lemma endo_preserves_zero : forall (a : СontinuousEndo), a zero = zero.
Proof.
  intro a.
  rewrite <- domain_lub_empty.
  rewrite endo_continuous with (X := Empty_set Domain) by assumption.
  
  assert (Im_empty : Im _ _ (Empty_set Domain) a = Empty_set Domain).
  {
    apply Extensionality_Ensembles.
    split.
    - intros y Hy. inversion Hy. contradiction.
    - intros y Hy. contradiction.
  }
  rewrite Im_empty.
  rewrite domain_lub_empty.
  reflexivity.
Qed.

Lemma endo_dot_ann_right : forall (x : СontinuousEndo), x * 0 = 0.
Proof.
  intros x.
  unfold dot, zero, Endo_MonoidOps, Endo_SemiLatticeOps; simpl.
  unfold compose.
  apply functional_extensionality.
  intro d.
  rewrite endo_preserves_zero.
  reflexivity.
Qed.

Instance СontinuousEndo_IdemSemiRing : IdemSemiRing (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (Lo := Endo_LeqOp) := {
    ISR_LHISR := Endo_LeftHandedIdemSemiRing;
    dot_ann_right := endo_dot_ann_right;
    dot_distr_right := endo_dot_distr_right
}.

Fixpoint iter (n : nat) (e : Endo) (d : Domain) : Domain :=
  match n with
  | O => d
  | S n' => let prev := iter n' e d in prev + e prev
  end.

Instance Endo_StarOp : Star_Op Endo := {
  star x := fun d s => fun t => exists n, In _ (iter n x d s) t;
}.

Lemma endo_star_destruct_left : forall (a b : Endo),
    a * b <== b -> a# * b <== b.
Proof.
Admitted.

Lemma endo_star_make_right : forall (x : Endo),
  1 + x * x# = x#.
Proof.
Admitted.

Instance Endo_LeftHandedKleneeAlgebra : LeftHandedKleneeAlgebra (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (So := Endo_StarOp) (Lo := Endo_LeqOp) := {
  LHKA_LHISR := Endo_LeftHandedIdemSemiRing;
  star_make_right := endo_star_make_right;
  star_destruct_left := endo_star_destruct_left
}.
