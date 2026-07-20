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

Lemma Im_singleton : forall U V (f : U -> V) (x : U),
    Im U V (Singleton U x) f = Singleton V (f x).
Proof.
  intros U V f x.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [z Hz y Hy]; destruct Hz; subst; constructor.
  - destruct Hy; apply Im_def; constructor.
Qed.

Lemma Im_union : forall U V (A B : Ensemble U) (f : U -> V),
    Im U V (Union U A B) f = Union V (Im U V A f) (Im U V B f).
Proof.
  intros U V A B f.
  apply Extensionality_Ensembles; split; intros y Hy.
  - destruct Hy as [x Hx y Hy]; subst.
    destruct Hx as [x Hx | x Hx]; [left | right]; apply Im_def, Hx.
  - destruct Hy as [y Hy | y Hy]; destruct Hy as [x Hx y Hy]; subst;
      apply Im_def; [left | right]; exact Hx.
Qed.

Lemma endo_continuous_binary : forall (a : СontinuousEndo) (x y : Domain),
    a (x + y) = a x + a y.
Proof.
  intros a x y.
  replace (x + y) with (domain_lub (Union _ (Singleton _ x) (Singleton _ y)))
    by now rewrite domain_lub_union, 2 domain_lub_singleton.
  now rewrite endo_continuous, Im_union, 2 Im_singleton,
              domain_lub_union, 2 domain_lub_singleton.
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

Lemma endo_leq_pointwise_into : forall (a b : Endo),
  (forall (x : Domain), a x <== b x) -> a <== b.
Proof.
  intros a b H.
  unfold leq, Endo_LeqOp.
  extensionality d.
  apply domain_leq_plus_def, H.
Qed.

Lemma endo_leq_pointwise_elim : forall (a b : Endo),
  forall (x : Domain), a <== b -> a x <== b x.
Proof.
  intros a b x H.
  apply domain_leq_plus_def.
  exact (f_equal (fun f => f x) H).
Qed.

Lemma endo_leq_refl : forall (a : Endo), a <== a.
Proof.
  intro a.
  apply endo_leq_pointwise_into; intro; apply domain_leq_refl.
Qed.

Lemma endo_leq_antisym : forall (x y : Endo),
    x <== y -> y <== x -> x = y.
Proof.
  intros x y Hxy Hyx.
  extensionality d.
  apply domain_leq_antisym; apply endo_leq_pointwise_elim; assumption.
Qed.

Lemma endo_leq_trans : forall (x y z : Endo),
    x <== y -> y <== z -> x <== z.
Proof.
  intros x y z Hxy Hyz.
  apply endo_leq_pointwise_into; intro d.
  apply (domain_leq_trans (x d) (y d) (z d));
    apply endo_leq_pointwise_elim; assumption.
Qed.

Instance Endo_PartiallyOrdered : PartiallyOrdered (Lo := Endo_LeqOp) := {
  leq_refl := endo_leq_refl;
  leq_antisym := endo_leq_antisym;
  leq_trans := endo_leq_trans;
}.

Lemma endo_leq_plus_def : forall (x y : Endo),
    x <== y <-> x + y = y.
Proof. intros x y; split; intro H; exact H. Qed.

Lemma endo_plus_neutral_left : forall (x : Endo),
    0 + x = x.
Proof. intro x; extensionality d; apply domain_plus_neutral_left. Qed.

Lemma endo_plus_idem : forall (x : Endo),
    x + x = x.
Proof. intro x; extensionality d; apply domain_plus_idem. Qed.

Lemma endo_plus_assoc : forall (x y z : Endo),
    x + (y + z) = (x + y) + z.
Proof. intros x y z; extensionality d; apply domain_plus_assoc. Qed.

Lemma endo_plus_com : forall (x y : Endo),
    x + y = y + x.
Proof. intros x y; extensionality d; apply domain_plus_com. Qed.

Instance Endo_SemiLattice : SemiLattice (SLo := Endo_SemiLatticeOps) (Lo := Endo_LeqOp) := {
    PO_SemiLattice := Endo_PartiallyOrdered;
    leq_plus_def := endo_leq_plus_def;
    plus_neutral_left := endo_plus_neutral_left;
    plus_idem := endo_plus_idem;
    plus_assoc := endo_plus_assoc;
    plus_com := endo_plus_com
}.

Lemma endo_plus_is_lub : forall (a b c : Endo),
  a <== c -> b <== c -> a + b <== c.
Proof.
  intros a b c Ha Hb.
  apply leq_plus_def.
  now rewrite <- plus_assoc, Hb, Ha.
Qed.

Lemma endo_plus_is_lub_left : forall (a b c : Endo),
  a + b <== c -> a <== c.
Proof.
  intros a b c H.
  unfold leq, Endo_LeqOp in *.
  now rewrite <- H, 2 plus_assoc, plus_idem.
Qed.

Lemma endo_plus_is_lub_right : forall (a b c : Endo),
  a + b <== c -> b <== c.
Proof.
  intros a b c H.
  rewrite plus_com in H.
  exact (endo_plus_is_lub_left b a c H).
Qed.

Lemma endo_leq_plus_left : forall (x y : Endo), x <== x + y.
Proof.
  intros x y; apply leq_plus_def.
  now rewrite plus_assoc, plus_idem.
Qed.

Lemma endo_leq_plus_right : forall (x y : Endo), y <== x + y.
Proof.
  intros x y; apply leq_plus_def.
  now rewrite (plus_com x y), plus_assoc, plus_idem.
Qed.

Lemma endo_dot_ann_left : forall (x : Endo), 0 * x = 0.
Proof. reflexivity. Qed.

Lemma endo_dot_distr_left : forall (x y z : Endo),
    (x + y) * z = x * z + y * z.
Proof. reflexivity. Qed.

Lemma endo_dot_monotone_left : forall (z : Endo) (x y : Endo),
    x <== y -> z * x <== z * y.
Proof.
  intros z x y Hleq.
  apply endo_leq_pointwise_into; intro d.
  apply (endo_monotone z (x d) (y d)).
  exact (endo_leq_pointwise_elim x y d Hleq).
Qed.

Lemma endo_dot_monotone_right : forall x y z, x <== y -> x * z <== y * z.
Proof.
  intros x y z H.
  unfold leq, Endo_LeqOp in *.
  now rewrite <- endo_dot_distr_left, H.
Qed.

Lemma endo_dot_distr_leq_right : forall (x y z : Endo),
    z * x + z * y <== z * (x + y).
Proof.
  intros x y z.
  apply endo_plus_is_lub; apply endo_dot_monotone_left;
    [ apply endo_leq_plus_left | apply endo_leq_plus_right ].
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
Proof. intros z x y; extensionality d; apply endo_continuous_binary. Qed.

Lemma endo_preserves_zero : forall (a : СontinuousEndo), a zero = zero.
Proof.
  intro a.
  now rewrite <- domain_lub_empty, endo_continuous, image_empty.
Qed.

Lemma endo_dot_ann_right : forall (x : СontinuousEndo), x * 0 = 0.
Proof. intro x; extensionality d; apply endo_preserves_zero. Qed.

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
  intro X; split.
  - intros f Hf.
    apply endo_leq_pointwise_into; intros d i t Ht.
    exists f; split; assumption.
  - intros g Hg.
    apply endo_leq_pointwise_into; intros d i t [f [Hf Ht]].
    exact (endo_leq_pointwise_elim f g d (Hg f Hf) i t Ht).
Qed.

Lemma Endo_sup_pointwise : forall (X : Ensemble Endo) (d : Domain),
    Endo_sup X d = domain_lub (Im _ _ X (fun f => f d)).
Proof.
  intros X d.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - destruct Ht as [f [Hf Ht]].
    exists (f d); split; [ exact (Im_intro _ _ X (fun f => f d) f Hf _ eq_refl) | exact Ht ].
  - destruct Ht as [g [Hg Ht]].
    destruct Hg as [f Hf g Hgeq]; subst.
    exists f; split; assumption.
Qed.

Lemma Endo_inf_is_glb : forall X, GLB X (Endo_inf X).
Proof.
  intro X; split.
  - intros f Hf.
    apply endo_leq_pointwise_into; intros d i t Ht.
    exact (Ht f Hf).
  - intros g Hg.
    apply endo_leq_pointwise_into; intros d i t Ht f Hf.
    exact (endo_leq_pointwise_elim g f d (Hg f Hf) i t Ht).
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
  apply domain_plus_monotone_left, endo_monotone, Hleq.
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
  apply endo_leq_pointwise_into; intro x.
  apply inf_is_glb.
  apply domain_plus_is_lub.
  - apply domain_leq_refl.
  - exact (endo_leq_pointwise_elim (a * b) b x H).
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
  - apply inf_is_glb; intros x Hx.
    apply (domain_leq_trans _ (d + a x) x).
    + apply domain_plus_monotone_left.
      apply inf_is_glb.
      unfold In, star_operator.
      rewrite <- endo_continuous_binary.
      apply endo_monotone, Hx.
    + exact Hx.

  - apply inf_is_glb.
    unfold In, star_operator.
    rewrite endo_continuous_binary.
    apply domain_plus_monotone_left.
    change (star_operator a (a d) (a# (a d)) <== a# (a d)).
    rewrite Endo_star_fixed_point_right.
    apply domain_leq_refl.
Qed.

Lemma endo_star_make_left : forall (x : СontinuousEndo),
    1 + x# * x = x#.
Proof.
  intro x.
  extensionality d.
  apply Endo_star_fixed_point_left.
Qed.

Fixpoint pow (a : Endo) (n : nat) : Endo :=
  match n with
    | O => 1
    | S n' => a * pow a n'
  end.

Lemma pow_in_powerset : forall (a : Endo) (n : nat) (d : Domain),
  In _ (Im _ _ (Im _ _ (Full_set nat) (pow a)) (fun f => f d)) ((pow a n) d).
Proof.
  intros a n d.
  exact (Im_intro _ _ (Im _ _ (Full_set nat) (pow a)) (fun f => f d) (pow a n)
           (Im_intro _ _ (Full_set nat) (pow a) n (Full_intro nat n) (pow a n) eq_refl)
           ((pow a n) d) eq_refl).
Qed.

Lemma star_sup_pow : forall (a : СontinuousEndo),
  a# = sup (Im _ _ (Full_set nat) (pow a)).
Proof.
  intro a.
  extensionality d.
  change (sup (Im _ _ (Full_set nat) (pow a)))
    with (Endo_sup (Im _ _ (Full_set nat) (pow a))).
  rewrite Endo_sup_pointwise.
  set (Pd := Im _ _ (Im _ _ (Full_set nat) (pow a)) (fun f => f d)).
  apply domain_leq_antisym.
  - apply inf_is_glb.
    unfold In, star_operator.
    apply domain_plus_is_lub.
    + apply (proj1 (Domain_sup_is_lub Pd)).
      exact (pow_in_powerset a 0 d).
    + rewrite endo_continuous.
      apply (proj2 (Domain_sup_is_lub (Im _ _ Pd a))).
      intros z Hz.
      destruct Hz as [y Hy z Hzeq];
        destruct Hy as [f Hf y Hyeq];
        destruct Hf as [n Hn f Hfeq]; subst.
      apply (proj1 (Domain_sup_is_lub Pd)).
      exact (pow_in_powerset a (S n) d).
  - apply (proj2 (Domain_sup_is_lub Pd)).
    intros y Hy.
    destruct Hy as [f Hf y Hyeq];
      destruct Hf as [n Hn f Hfeq]; subst.
    clear Hn.
    induction n.
    + change (pow a 0 d) with d.
      apply (domain_leq_trans d (star_operator a d (a# d)) (a# d)).
      * unfold star_operator; apply domain_leq_plus_left.
      * rewrite Endo_star_fixed_point_right; apply domain_leq_refl.
    + change (pow a (S n) d) with (a (pow a n d)).
      apply (domain_leq_trans (a (pow a n d)) (a (a# d)) (a# d)).
      * apply endo_monotone; exact IHn.
      * apply (domain_leq_trans (a (a# d)) (star_operator a d (a# d)) (a# d)).
        -- unfold star_operator; apply domain_leq_plus_right.
        -- rewrite Endo_star_fixed_point_right; apply domain_leq_refl.
Qed.

Lemma endo_dot_sup_left : forall (b : СontinuousEndo) (X : Ensemble Endo),
    b * (sup X) = sup (Im _ _ X (fun x => b * x)).
Proof.
  intros b X.
  extensionality d.
  change ((b * sup X) d) with (b (sup X d)).
  change (sup X) with (Endo_sup X); change (sup (Im _ _ X (fun x => b * x)))
    with (Endo_sup (Im _ _ X (fun x => b * x))).
  rewrite Endo_sup_pointwise, endo_continuous, Endo_sup_pointwise.
  f_equal.
  apply Extensionality_Ensembles; split; intros g Hg.
  - destruct Hg as [y Hy g Hgeq]; destruct Hy as [f Hf y Hyeq]; subst.
    apply (Im_intro _ _ (Im _ _ X (fun x => b * x)) (fun h => h d) (b * f)).
    + exact (Im_intro _ _ X (fun x => b * x) f Hf _ eq_refl).
    + reflexivity.
  - destruct Hg as [y Hy g Hgeq]; destruct Hy as [f Hf y Hyeq]; subst.
    apply (Im_intro _ _ (Im _ _ X (fun f => f d)) b (f d)).
    + exact (Im_intro _ _ X (fun f => f d) f Hf _ eq_refl).
    + reflexivity.
Qed.

Lemma endo_star_destruct_right : forall (a b : СontinuousEndo),
    b * a <== b -> b * a# <== b.
Proof.
  intros a b Hba.
  rewrite star_sup_pow, endo_dot_sup_left.
  apply sup_is_lub.
  intros f [g [n _ Hg] Hf]; subst.
  induction n.
  - apply leq_refl.
  - change (b * a * pow a n <== b).
    apply (leq_trans (b * a * pow a n) (b * pow a n) b).
    + exact (endo_dot_monotone_right (b * a) b (pow a n) Hba).
    + exact IHn.
Qed.

Instance СontinuousEndo_KleeneAlgebra : KleeneAlgebra (Mo := Endo_MonoidOps) (SLo := Endo_SemiLatticeOps) (So := Endo_StarOp) (Lo := Endo_LeqOp) := {
  KA_LHKA := Endo_LeftHandedKleneeAlgebra;
  KA_ISR := СontinuousEndo_IdemSemiRing;
  star_make_left := endo_star_make_left;
  star_destruct_right := endo_star_destruct_right
}.
