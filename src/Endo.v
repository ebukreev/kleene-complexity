From klenee_complexity Require Import Algebraic_Structures Domain Conf LFP NEList.
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
      + destruct Hw. left. red. rewrite <- H0. constructor.
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
  apply functional_extensionality.
  intro d.
  apply domain_plus_idem.
Qed.

Lemma endo_leq_antisym : forall (x y : Endo), 
    x <== y -> y <== x -> x = y.
Proof.
  intros x y Hxy Hyx.
  extensionality d.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t Ht.
    apply (f_equal (fun f => f d i)) in Hxy.
    simpl in Hxy.
    assert (H : In Trace (Union Trace (x d i) (y d i)) t).
    { apply Union_introl; assumption. }
    rewrite Hxy in H.
    assumption.
  - intros t Ht.
    apply (f_equal (fun f => f d i)) in Hyx.
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
  extensionality d.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t Ht.
    inversion Ht as [t' H1 | t' H2].
    + pose proof (f_equal (fun f => f d i) Hxy) as Hxy'.
      assert (Ht_y : In Trace (y d i) t).
      {
        rewrite <- Hxy'.
        apply Union_introl.
        assumption.
      }
      pose proof (f_equal (fun f => f d i) Hyz) as Hyz'.
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

Lemma endo_leq_pointwise_into : forall (a b : Endo),
  (forall (x : Domain), a x <== b x) -> a <== b.
Proof.
  intros a b H.
  unfold leq, Endo_LeqOp.
  extensionality d.
  specialize (H d).
  apply domain_leq_plus_def.
  assumption.
Qed.

Lemma endo_leq_pointwise_elim : forall (a b : Endo),
  forall (x : Domain), a <== b -> a x <== b x.
Proof.
  intros a b x H.
  unfold leq, Endo_LeqOp in H.
  apply domain_leq_plus_def.
  assert (H1 : a x + b x = (a + b) x) by reflexivity. 
  rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Lemma endo_plus_neutral_left : forall (x : Endo), 
    0 + x = x.
Proof.
  intros x.
  extensionality d.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H. inversion H; [inversion H0 | assumption].
  - intros t H. apply Union_intror; assumption.
Qed.

Lemma endo_plus_idem : forall (x : Endo), 
    x + x = x.
Proof.
  intros x.
  extensionality d.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H. inversion H; assumption.
  - intros t H. apply Union_introl; assumption.
Qed.

Lemma endo_plus_assoc : forall (x y z : Endo), 
    x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  extensionality d.
  extensionality i.
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
  extensionality d.
  extensionality i.
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
  extensionality d.
  extensionality i.
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
  reflexivity.
Qed.

Lemma endo_dot_monotone_left : forall (z : Endo) (x y : Endo),
    x <== y -> z * x <== z * y.
Proof.
  intros z x y Hleq.
  apply functional_extensionality.
  intro d.
  extensionality i.
  
  assert (x_d_le_y_d : x d <== y d).
  {
    intro j.
    pose proof (f_equal (fun f => f d j) Hleq) as Heq.
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

Lemma endo_dot_monotone_right : forall x y z, x <== y -> x * z <== y * z.
Proof.
  intros x y z H.
  unfold leq, Endo_LeqOp in H.
  unfold leq, Endo_LeqOp.
  rewrite <- endo_dot_distr_left.
  rewrite H.
  reflexivity.
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

Lemma plus_is_lub_left: forall (a b c : Endo),
  a + b <== c -> a <== c.
Proof.
  intros a b c H.
  unfold leq, Endo_LeqOp in H.
  unfold leq, Endo_LeqOp.
  rewrite <- H.
  rewrite 2 plus_assoc.
  rewrite plus_idem.
  reflexivity.
Qed.

Lemma plus_is_lub_right: forall (a b c : Endo),
  a + b <== c -> b <== c.
Proof.
  intros a b c H. 
  rewrite plus_com in H.
  apply (plus_is_lub_left b a c H).
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
  { apply endo_dot_monotone_left. assumption. }
  
  assert (Hzy : z * y <== z * (x + y)).
  { apply endo_dot_monotone_left. assumption. }

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
  extensionality d.
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

Definition Endo_sup (X : Ensemble Endo) : Endo :=
  fun d i t => exists f, In _ X f /\ In _ (f d i) t.

Definition Endo_inf (X : Ensemble Endo) : Endo :=
  fun d i t => forall f, In _ X f -> In _ (f d i) t.

Lemma Endo_sup_is_lub : forall X, LUB X (Endo_sup X).
Proof.
  intro X.
  constructor.
  - intros f Hf_in_X.
    apply functional_extensionality.
    intro d.
    apply leq_plus_def.
    intros i t Ht.
    exists f.
    split; assumption.
  - intros g H_g_upper_bound.
    apply functional_extensionality.
    intro d.
    apply leq_plus_def.
    intros i t Ht.
    destruct Ht as [f [Hf_in_X Ht_in_f]].
    specialize (H_g_upper_bound f Hf_in_X).
    apply (f_equal (fun h => h d)) in H_g_upper_bound.
    apply domain_leq_plus_def in H_g_upper_bound.
    specialize (H_g_upper_bound i).
    apply H_g_upper_bound.
    assumption.
Qed.
  
Lemma Endo_inf_is_glb : forall X, GLB X (Endo_inf X).
Proof.
  intro X.
  constructor.
  - intros f Hf_in_X.
    apply functional_extensionality.
    intro d.
    apply leq_plus_def.
    intros i t Ht.
    apply Ht.
    assumption.
  - intros g H_g_lower_bound.
    apply functional_extensionality.
    intro d.
    apply leq_plus_def.
    intros i t Ht f Hf_in_X.
    specialize (H_g_lower_bound f Hf_in_X).
    apply (f_equal (fun h => h d)) in H_g_lower_bound.
    apply domain_leq_plus_def in H_g_lower_bound.
    specialize (H_g_lower_bound i).
    apply H_g_lower_bound.
    assumption.
Qed.

Instance Endo_CompleteLattice : CompleteLattice (Lo := Endo_LeqOp) := {
  PO_CompleteLattice := Endo_PartiallyOrdered;
  sup := Endo_sup;
  sup_is_lub := Endo_sup_is_lub;
  inf := Endo_inf;
  inf_is_glb := Endo_inf_is_glb;
}.

Definition star_operator (a : Endo) (d : Domain) : Endo :=
  fun (x : Domain) => d + a x.

Lemma star_operator_monotone (a : Endo) (d : Domain) : Monotone (star_operator a d).
Proof.
  unfold Monotone, star_operator.
  intros x y Hleq.
  apply domain_plus_monotone_left.
  apply endo_monotone.
  assumption.
Qed.

Instance Endo_StarOp : Star_Op Endo := {
  star a := fun d => lfp (star_operator a d) (star_operator_monotone a d)
}.

Lemma Endo_star_fixed_point_right (a : Endo) (d : Domain) :
  star_operator a d (a# d) = (a# d).
Proof.
  apply lfp_is_fixed_point.
Qed.

Lemma endo_star_make_right : forall (x : Endo),
    1 + x * x# = x#.
Proof.
  intro x.
  extensionality d.
  apply Endo_star_fixed_point_right.
Qed.

Lemma endo_star_destruct_left : forall (a b : Endo),
    a*b <== b -> a#*b <== b.
Proof.
  intros a b H.

  assert (forall x, star_operator a (b x) (b x) <== (b x)).
  {
    intro x.
    apply domain_plus_is_lub.
    apply domain_leq_refl.
    assert (H1 : (a * b) x <== b x). {
      apply endo_leq_pointwise_elim.
      assumption.
    }
    assumption.
  }

  apply endo_leq_pointwise_into.
  intro x.
  specialize (H0 x).
  apply (domain_leq_trans ((a # * b) x) (star_operator a (b x) (b x)) (b x)).
  - apply inf_is_glb.
    apply endo_monotone.
    assumption.
  - assumption.
Qed.

Instance Endo_LeftHandedKleneeAlgebra : LeftHandedKleneeAlgebra (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (So := Endo_StarOp) (Lo := Endo_LeqOp) := {
  LHKA_LHISR := Endo_LeftHandedIdemSemiRing;
  star_make_right := endo_star_make_right;
  star_destruct_left := endo_star_destruct_left
}.

Lemma Endo_star_fixed_point_left (a : СontinuousEndo) (d : Domain) :
  star_operator (a#) d (a d) = (a# d).
Proof.
  apply leq_antisym.

  - apply inf_is_glb.
    intros x H.
  
    set (P := fun x : Domain => a d + a x <== x).
    apply (domain_leq_trans (d + inf P) (d + a x) x).
    + apply domain_plus_monotone_left.
      destruct (inf_is_glb P) as [H_lower _].
      apply H_lower.
      unfold In.
      assert (a (d + (a x)) = a d + a (a x)). 
      {
        apply endo_continuous_binary.
      }
      unfold P.
      rewrite <- H0.
      apply endo_monotone.
      assumption.
    + assumption.

  - apply inf_is_glb.
    unfold star_operator.
    apply endo_monotone.

    set (P := fun x : Domain => a d + a x <== x).
    intros s t Ht x Hx_P.
  
    destruct (inf_is_glb P) as [H_lower _].

    assert (H_sum : d + inf P <== d + x).
    { apply domain_plus_monotone_left. apply H_lower. exact Hx_P. }

    assert (H_a_mono : a (d + inf P) <== a (d + x)).
    { apply endo_monotone. exact H_sum. }

    assert (H : forall x, a (d + x) = a d + a x).
    { intro. apply endo_continuous_binary. }

    rewrite H in H_a_mono.

    assert (H0 : a (d + inf P) <== x).
    { apply (domain_leq_trans (a (d + inf P)) (a d + a x) x).
      - rewrite <- H. apply endo_monotone. assumption.
      - exact Hx_P. }

    specialize (H0 s).

    apply H0.
    assumption.
Qed.

Lemma endo_star_make_left : forall (x : СontinuousEndo),
    1 + x# * x = x#.
Proof.
  intro x.
  extensionality d.
  apply Endo_star_fixed_point_left.
Qed.

Lemma endo_plus_is_lub : forall x y z,
  x <== z -> y <== z -> x + y <== z.
Proof.
  intros x y z H1 H2.
  apply leq_plus_def.
  rewrite leq_plus_def in H1.
  rewrite leq_plus_def in H2.
  rewrite <- plus_assoc.
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

Fixpoint pow (a : Endo) (n : nat) : Endo :=
  match n with
    | O => 1
    | S n' => a * pow a n'
  end.

Axiom star_sup_pow : forall (a : СontinuousEndo), 
  a# = sup (Im _ _ (Full_set nat) (pow a)).

Axiom endo_dot_sup_left : forall (b : СontinuousEndo) (X : Ensemble Endo),
    b * (sup X) = sup (Im _ _ X (fun x => b * x)).

Lemma endo_star_destruct_right : forall (a b : СontinuousEndo),
    b * a <== b -> b * a# <== b.
Proof.
  intros a b Hba.  
  rewrite star_sup_pow.

  set (P := fun (f : Endo) => b * f <== b).
  assert (P_sup_chain : forall (g : nat -> Endo),
      (forall n, P (g n)) -> P (sup (Im nat Endo (Full_set nat) g))).
  {
    intros g H.
    unfold P.
    rewrite endo_dot_sup_left.

    apply functional_extensionality.
    intro d.
    apply leq_plus_def.
    intros i t Ht.
    destruct Ht as [h [Hh_in_Im Ht_in_h]].
    destruct Hh_in_Im as [f Hf_in_Im Hh_eq].
    destruct Hf_in_Im as [n _ Hf_eq].
    subst Hf_eq Hh_eq.
  
    specialize (H n).
  
    assert (H_sub : Included Trace ((b * g n) d i) (b d i)).
    {
      intros x Hx.
      assert (H_union : In Trace ((b * g n + b) d i) x).
      {
        apply Union_introl.
        exact Hx.
      }
      assert (Hin: In Trace (b d i) x).
      {
        rewrite <- H.
        exact H_union.
      }
      assumption.
    }
    
    apply H_sub.
    exact Ht_in_h.
  }

  apply P_sup_chain.

  induction n.
  - unfold P, pow.
    rewrite dot_neutral_right. 
    apply leq_refl.
  - assert (P_closed : forall f, P f -> P (a * f)).
    {
      intros f Hf.
      unfold P.
      rewrite dot_assoc.
      apply (leq_trans ((b * a) * f) (b * f) b).
      - apply endo_dot_monotone_right. 
        exact Hba.
      - exact Hf.
    }
    apply P_closed. 
    assumption.
Qed.
    
Instance СontinuousEndo_KleeneAlgebra : KleeneAlgebra (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (So := Endo_StarOp) (Lo := Endo_LeqOp) := {
  KA_LHKA := Endo_LeftHandedKleneeAlgebra;
  KA_ISR := СontinuousEndo_IdemSemiRing;
  star_make_left := endo_star_make_left;
  star_destruct_right := endo_star_destruct_right
}.
