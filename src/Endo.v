From klenee_complexity Require Import Algebraic_Structures Domain Conf LFP NEList Image_Facts.
From Coq Require Import Program.Basics Strings.String.
From Coq Require Import Sets.Powerset Sets.Image.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ProofIrrelevance.

Definition Endo := Domain -> Domain.

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

Lemma endo_dot_distr_left : forall (x y z : Endo),
    (x + y) * z = x * z + y * z.
Proof. reflexivity. Qed.

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

Lemma star_operator_monotone (a : Endo) (d : Domain) (Hm : Monotone a) :
  Monotone (star_operator a d).
Proof.
  unfold Monotone, star_operator.
  intros x y Hleq.
  apply domain_plus_monotone_left, Hm, Hleq.
Qed.

Definition endo_star (a : Endo) (Hm : Monotone a) : Endo :=
  fun d => lfp (star_operator a d) (star_operator_monotone a d Hm).

Lemma Endo_star_fixed_point_right (a : Endo) (Hm : Monotone a) (d : Domain) :
  star_operator a d (endo_star a Hm d) = (endo_star a Hm d).
Proof.
  apply lfp_is_fixed_point.
Qed.

Lemma endo_star_make_right : forall (x : Endo) (Hm : Monotone x),
    1 + x * endo_star x Hm = endo_star x Hm.
Proof.
  intros x Hm.
  extensionality d.
  apply Endo_star_fixed_point_right.
Qed.

Lemma endo_star_destruct_left : forall (a b : Endo) (Hm : Monotone a),
    a * b <== b -> endo_star a Hm * b <== b.
Proof.
  intros a b Hm H.
  apply endo_leq_pointwise_into; intro x.
  apply inf_is_glb.
  apply domain_plus_is_lub.
  - apply domain_leq_refl.
  - exact (endo_leq_pointwise_elim (a * b) b x H).
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

Lemma endo_dot_monotone_left : forall (z : Endo), Monotone z ->
    forall (x y : Endo), x <== y -> z * x <== z * y.
Proof.
  intros z Hm x y Hleq.
  apply endo_leq_pointwise_into; intro d.
  apply (Hm (x d) (y d)).
  exact (endo_leq_pointwise_elim x y d Hleq).
Qed.

Lemma endo_dot_monotone_right : forall x y z, x <== y -> x * z <== y * z.
Proof.
  intros x y z H.
  unfold leq, Endo_LeqOp in *.
  now rewrite <- endo_dot_distr_left, H.
Qed.

Lemma endo_dot_distr_leq_right : forall (z : Endo), Monotone z ->
    forall (x y : Endo), z * x + z * y <== z * (x + y).
Proof.
  intros z Hm x y.
  apply endo_plus_is_lub; apply (endo_dot_monotone_left z Hm);
    [ apply endo_leq_plus_left | apply endo_leq_plus_right ].
Qed.

Lemma endo_star_monotone_in_d : forall (a : Endo) (Hm : Monotone a),
    Monotone (endo_star a Hm).
Proof.
  intros a Hm d1 d2 Hd.
  unfold endo_star.
  apply lfp_leq.
  intro x; unfold star_operator.
  rewrite (domain_plus_com d1 (a x)), (domain_plus_com d2 (a x)).
  apply domain_plus_monotone_left; exact Hd.
Qed.

Lemma id_monotone : Monotone (@id Domain).
Proof. intros x y H; exact H. Qed.

Lemma compose_monotone : forall (f g : Endo),
    Monotone f -> Monotone g -> Monotone (compose f g).
Proof.
  intros f g Hf Hg x y H; unfold compose.
  apply Hf, Hg, H.
Qed.

Lemma czero_monotone : Monotone (fun _ : Domain => (zero : Domain)).
Proof. intros x y H; apply domain_leq_refl. Qed.

Lemma cplus_monotone : forall (a b : Endo),
    Monotone a -> Monotone b -> Monotone (fun d => a d + b d).
Proof.
  intros a b Ha Hb x y H.
  apply domain_plus_is_lub.
  - apply (domain_leq_trans _ (a y) _); [ apply Ha; exact H | apply domain_leq_plus_left ].
  - apply (domain_leq_trans _ (b y) _); [ apply Hb; exact H | apply domain_leq_plus_right ].
Qed.

Lemma domain_lub_Im_plus : forall (a b : Endo) (X : Ensemble Domain),
    domain_lub (Im _ _ X (fun d => a d + b d))
    = domain_lub (Im _ _ X a) + domain_lub (Im _ _ X b).
Proof.
  intros a b X.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - destruct Ht as [D [HD Ht]]; destruct HD as [x Hx D HDeq]; subst D.
    destruct Ht as [t Ht | t Ht].
    + left; exists (a x); split; [ exact (Im_intro _ _ X a x Hx _ eq_refl) | exact Ht ].
    + right; exists (b x); split; [ exact (Im_intro _ _ X b x Hx _ eq_refl) | exact Ht ].
  - destruct Ht as [t Ht | t Ht]; destruct Ht as [D [HD Ht]];
      destruct HD as [x Hx D HDeq]; subst D;
      exists (a x + b x); split;
      try (exact (Im_intro _ _ X (fun d => a d + b d) x Hx _ eq_refl)).
    + apply Union_introl; exact Ht.
    + apply Union_intror; exact Ht.
Qed.

Lemma sig_eq : forall {A} {P : A -> Prop} (a b : sig P),
    proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros A P [f Hf] [g Hg] H; simpl in H; subst g.
  f_equal; apply proof_irrelevance.
Qed.

Definition MonotoneEndo := { f : Endo | Monotone f }.

Definition me_fn (a : MonotoneEndo) : Endo := proj1_sig a.
Definition me_mono (a : MonotoneEndo) : Monotone (me_fn a) := proj2_sig a.

Definition me_one : MonotoneEndo := exist _ (@id Domain) id_monotone.
Definition me_dot (a b : MonotoneEndo) : MonotoneEndo :=
  exist _ (compose (me_fn a) (me_fn b)) (compose_monotone _ _ (me_mono a) (me_mono b)).
Definition me_zero : MonotoneEndo := exist _ (fun _ => zero) czero_monotone.
Definition me_plus (a b : MonotoneEndo) : MonotoneEndo :=
  exist _ (fun d => me_fn a d + me_fn b d) (cplus_monotone _ _ (me_mono a) (me_mono b)).
Definition me_star (a : MonotoneEndo) : MonotoneEndo :=
  exist _ (endo_star (me_fn a) (me_mono a)) (endo_star_monotone_in_d (me_fn a) (me_mono a)).

Instance ME_MonoidOps : Monoid_Ops MonotoneEndo := { one := me_one; dot := me_dot }.
Instance ME_SemiLatticeOps : SemiLattice_Ops MonotoneEndo := { zero := me_zero; plus := me_plus }.
Instance ME_LeqOp : Leq_Op MonotoneEndo := { leq a b := me_fn a <== me_fn b }.
Instance ME_StarOp : Star_Op MonotoneEndo := { star := me_star }.

Instance ME_Monoid : Monoid (Mo := ME_MonoidOps).
Proof. split; intros; apply sig_eq; reflexivity. Qed.

Instance ME_PartiallyOrdered : PartiallyOrdered (Lo := ME_LeqOp).
Proof.
  split.
  - intro a; apply endo_leq_refl.
  - intros x y Hxy Hyx; apply sig_eq; apply endo_leq_antisym; assumption.
  - intros x y z; apply endo_leq_trans.
Qed.

Instance ME_SemiLattice : SemiLattice (SLo := ME_SemiLatticeOps) (Lo := ME_LeqOp).
Proof.
  refine {| PO_SemiLattice := ME_PartiallyOrdered |}; intros.
  - split; intro H.
    + apply sig_eq; apply (proj1 (endo_leq_plus_def _ _)); exact H.
    + change (me_fn x <== me_fn y);
        apply (proj2 (endo_leq_plus_def _ _)); exact (f_equal me_fn H).
  - apply sig_eq; apply endo_plus_neutral_left.
  - apply sig_eq; apply endo_plus_idem.
  - apply sig_eq; apply endo_plus_assoc.
  - apply sig_eq; apply endo_plus_com.
Qed.

Instance ME_LeftHandedIdemSemiRing :
    LeftHandedIdemSemiRing (Mo := ME_MonoidOps) (SLo := ME_SemiLatticeOps) (Lo := ME_LeqOp).
Proof.
  refine {| LHISR_Monoid := ME_Monoid; LHISR_SemiLattice := ME_SemiLattice |}; intros.
  - apply sig_eq; reflexivity.
  - apply sig_eq; reflexivity.
  - apply (endo_dot_distr_leq_right (me_fn z) (me_mono z)).
Qed.

Instance ME_LeftHandedKleneeAlgebra :
    LeftHandedKleneeAlgebra (Mo := ME_MonoidOps) (SLo := ME_SemiLatticeOps)
                            (So := ME_StarOp) (Lo := ME_LeqOp).
Proof.
  refine {| LHKA_LHISR := ME_LeftHandedIdemSemiRing |}; intros.
  - apply sig_eq; apply endo_star_make_right.
  - apply (endo_star_destruct_left (me_fn a) (me_fn b) (me_mono a) H).
Qed.

Definition Continuous (a : Endo) : Prop :=
  forall (X : Ensemble Domain), a (domain_lub X) = domain_lub (Im _ _ X a).

Lemma endo_continuous_binary : forall (a : Endo), Continuous a ->
    forall (x y : Domain), a (x + y) = a x + a y.
Proof.
  intros a Hc x y.
  replace (x + y) with (domain_lub (Union _ (Singleton _ x) (Singleton _ y)))
    by now rewrite domain_lub_union, 2 domain_lub_singleton.
  now rewrite Hc, Im_union, 2 Im_singleton,
              domain_lub_union, 2 domain_lub_singleton.
Qed.

Lemma endo_dot_distr_right : forall (z : Endo), Continuous z ->
    forall (x y : Endo), z * (x + y) = z * x + z * y.
Proof. intros z Hc x y; extensionality d; apply endo_continuous_binary, Hc. Qed.

Lemma endo_preserves_zero : forall (a : Endo), Continuous a -> a zero = zero.
Proof.
  intros a Hc.
  now rewrite <- domain_lub_empty, Hc, image_empty.
Qed.

Lemma endo_dot_ann_right : forall (x : Endo), Continuous x -> x * 0 = 0.
Proof. intros x Hc; extensionality d; apply endo_preserves_zero, Hc. Qed.

Lemma Endo_star_fixed_point_left (a : Endo) (Hc : Continuous a) (Hm : Monotone a) (d : Domain) :
  star_operator (endo_star a Hm) d (a d) = (endo_star a Hm d).
Proof.
  apply leq_antisym.
  - apply inf_is_glb; intros x Hx.
    apply (domain_leq_trans _ (d + a x) x).
    + apply domain_plus_monotone_left.
      apply inf_is_glb.
      unfold In, star_operator.
      rewrite <- (endo_continuous_binary a Hc).
      apply Hm, Hx.
    + exact Hx.

  - apply inf_is_glb.
    unfold In, star_operator.
    rewrite (endo_continuous_binary a Hc).
    apply domain_plus_monotone_left.
    change (star_operator a (a d) (endo_star a Hm (a d)) <== endo_star a Hm (a d)).
    rewrite Endo_star_fixed_point_right.
    apply domain_leq_refl.
Qed.

Lemma endo_star_make_left : forall (x : Endo) (Hc : Continuous x) (Hm : Monotone x),
    1 + endo_star x Hm * x = endo_star x Hm.
Proof.
  intros x Hc Hm.
  extensionality d.
  apply Endo_star_fixed_point_left, Hc.
Qed.

Lemma pow_continuous : forall (a : Endo), Continuous a ->
    forall n, Continuous (pow a n).
Proof.
  intros a Hc.
  induction n as [| n IH].
  - intro X.
    change (pow a 0) with (@id Domain).
    rewrite Im_id.
    reflexivity.
  - intro X.
    change (pow a (S n)) with (compose a (pow a n)).
    unfold compose at 1.
    rewrite (IH X), (Hc (Im _ _ X (pow a n))), Im_compose.
    reflexivity.
Qed.

Lemma star_sup_pow : forall (a : Endo) (Hc : Continuous a) (Hm : Monotone a),
  endo_star a Hm = sup (Im _ _ (Full_set nat) (pow a)).
Proof.
  intros a Hc Hm.
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
    + rewrite (Hc Pd).
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
      apply (domain_leq_trans d (star_operator a d (endo_star a Hm d)) (endo_star a Hm d)).
      * unfold star_operator; apply domain_leq_plus_left.
      * rewrite Endo_star_fixed_point_right; apply domain_leq_refl.
    + change (pow a (S n) d) with (a (pow a n d)).
      apply (domain_leq_trans (a (pow a n d)) (a (endo_star a Hm d)) (endo_star a Hm d)).
      * apply Hm; exact IHn.
      * apply (domain_leq_trans (a (endo_star a Hm d)) (star_operator a d (endo_star a Hm d)) (endo_star a Hm d)).
        -- unfold star_operator; apply domain_leq_plus_right.
        -- rewrite Endo_star_fixed_point_right; apply domain_leq_refl.
Qed.

Lemma endo_star_mem : forall (a : Endo) (Hc : Continuous a) (Hm : Monotone a)
                             (d : Domain) (i : string) (t : Trace),
    In _ (endo_star a Hm d i) t <-> exists n, In _ (pow a n d i) t.
Proof.
  intros a Hc Hm d i t.
  assert (Hd : endo_star a Hm d
             = domain_lub (Im _ _ (Im _ _ (Full_set nat) (pow a)) (fun f => f d))).
  { rewrite (star_sup_pow a Hc Hm).
    change (sup (Im _ _ (Full_set nat) (pow a)))
      with (Endo_sup (Im _ _ (Full_set nat) (pow a))).
    apply Endo_sup_pointwise. }
  rewrite Hd; split.
  - intros [D [HD Ht]].
    destruct HD as [g Hg D HDeq]; subst D.
    destruct Hg as [n Hn g Hgeq]; subst g.
    exists n; exact Ht.
  - intros [n Ht].
    exists (pow a n d); split; [ exact (pow_in_powerset a n d) | exact Ht ].
Qed.

Lemma endo_star_continuous : forall (a : Endo) (Hc : Continuous a) (Hm : Monotone a),
    Continuous (endo_star a Hm).
Proof.
  intros a Hc Hm X.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - apply (proj1 (endo_star_mem a Hc Hm (domain_lub X) i t)) in Ht.
    destruct Ht as [n Ht].
    rewrite (pow_continuous a Hc n X) in Ht.
    destruct Ht as [D [HD Ht]].
    destruct HD as [x Hx D HDeq]; subst D.
    exists (endo_star a Hm x); split.
    + exact (Im_intro _ _ X (endo_star a Hm) x Hx _ eq_refl).
    + apply (proj2 (endo_star_mem a Hc Hm x i t)).
      exists n; exact Ht.
  - destruct Ht as [D [HD Ht]].
    destruct HD as [x Hx D HDeq]; subst D.
    apply (proj1 (endo_star_mem a Hc Hm x i t)) in Ht.
    destruct Ht as [n Ht].
    apply (proj2 (endo_star_mem a Hc Hm (domain_lub X) i t)).
    exists n.
    rewrite (pow_continuous a Hc n X).
    exists (pow a n x); split.
    + exact (Im_intro _ _ X (pow a n) x Hx _ eq_refl).
    + exact Ht.
Qed.

Lemma endo_dot_sup_left : forall (b : Endo), Continuous b ->
    forall (X : Ensemble Endo),
    b * (sup X) = sup (Im _ _ X (fun x => b * x)).
Proof.
  intros b Hc X.
  extensionality d.
  change ((b * sup X) d) with (b (sup X d)).
  change (sup X) with (Endo_sup X); change (sup (Im _ _ X (fun x => b * x)))
    with (Endo_sup (Im _ _ X (fun x => b * x))).
  rewrite Endo_sup_pointwise, (Hc _), Endo_sup_pointwise.
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

Lemma endo_star_destruct_right : forall (a b : Endo)
                                        (Hca : Continuous a) (Hma : Monotone a)
                                        (Hcb : Continuous b),
    b * a <== b -> b * endo_star a Hma <== b.
Proof.
  intros a b Hca Hma Hcb Hba.
  rewrite (star_sup_pow a Hca Hma), (endo_dot_sup_left b Hcb).
  apply sup_is_lub.
  intros f [g [n _ Hg] Hf]; subst.
  induction n.
  - apply leq_refl.
  - change (b * a * pow a n <== b).
    apply (leq_trans (b * a * pow a n) (b * pow a n) b).
    + exact (endo_dot_monotone_right (b * a) b (pow a n) Hba).
    + exact IHn.
Qed.

Lemma id_continuous : Continuous (@id Domain).
Proof. intro X; unfold id; rewrite Im_id; reflexivity. Qed.

Lemma czero_continuous : Continuous (fun _ : Domain => (zero : Domain)).
Proof.
  intro X.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - destruct Ht.
  - destruct Ht as [D [HD Ht]]; destruct HD as [x Hx D HDeq]; subst D; destruct Ht.
Qed.

Lemma compose_continuous : forall (f g : Endo),
    Continuous f -> Continuous g -> Continuous (compose f g).
Proof.
  intros f g Hf Hg X; unfold compose.
  rewrite (Hg X), (Hf (Im _ _ X g)), Im_compose.
  reflexivity.
Qed.

Lemma cplus_continuous : forall (a b : Endo),
    Continuous a -> Continuous b -> Continuous (fun d => a d + b d).
Proof.
  intros a b Ha Hb X.
  change ((fun d => a d + b d) (domain_lub X)) with (a (domain_lub X) + b (domain_lub X)).
  rewrite (Ha X), (Hb X).
  symmetry; apply domain_lub_Im_plus.
Qed.

Definition СontinuousEndo := { f : MonotoneEndo | Continuous (me_fn f) }.

Definition ce_me (a : СontinuousEndo) : MonotoneEndo := proj1_sig a.
Definition ce_fn (a : СontinuousEndo) : Endo := me_fn (ce_me a).
Definition ce_mono (a : СontinuousEndo) : Monotone (ce_fn a) := me_mono (ce_me a).
Definition ce_cont (a : СontinuousEndo) : Continuous (ce_fn a) := proj2_sig a.

Lemma ce_eq : forall (a b : СontinuousEndo), ce_fn a = ce_fn b -> a = b.
Proof. intros a b H; apply sig_eq, sig_eq, H. Qed.

Definition ce_one : СontinuousEndo := exist _ me_one id_continuous.
Definition ce_dot (a b : СontinuousEndo) : СontinuousEndo :=
  exist _ (me_dot (ce_me a) (ce_me b)) (compose_continuous _ _ (ce_cont a) (ce_cont b)).
Definition ce_zero : СontinuousEndo := exist _ me_zero czero_continuous.
Definition ce_plus (a b : СontinuousEndo) : СontinuousEndo :=
  exist _ (me_plus (ce_me a) (ce_me b)) (cplus_continuous _ _ (ce_cont a) (ce_cont b)).
Definition ce_star (a : СontinuousEndo) : СontinuousEndo :=
  exist _ (me_star (ce_me a)) (endo_star_continuous (ce_fn a) (ce_cont a) (ce_mono a)).

Instance СE_MonoidOps : Monoid_Ops СontinuousEndo := { one := ce_one; dot := ce_dot }.
Instance СE_SemiLatticeOps : SemiLattice_Ops СontinuousEndo := { zero := ce_zero; plus := ce_plus }.
Instance СE_LeqOp : Leq_Op СontinuousEndo := { leq a b := ce_me a <== ce_me b }.
Instance СE_StarOp : Star_Op СontinuousEndo := { star := ce_star }.

Instance СE_Monoid : Monoid (Mo := СE_MonoidOps).
Proof.
  split.
  - intros x y z; apply sig_eq; exact (dot_assoc (ce_me x) (ce_me y) (ce_me z)).
  - intro x; apply sig_eq; exact (dot_neutral_left (ce_me x)).
  - intro x; apply sig_eq; exact (dot_neutral_right (ce_me x)).
Qed.

Instance СE_PartiallyOrdered : PartiallyOrdered (Lo := СE_LeqOp).
Proof.
  split.
  - intro a; exact (leq_refl (ce_me a)).
  - intros x y Hxy Hyx; apply sig_eq; exact (leq_antisym (ce_me x) (ce_me y) Hxy Hyx).
  - intros x y z Hxy Hyz; exact (leq_trans (ce_me x) (ce_me y) (ce_me z) Hxy Hyz).
Qed.

Instance СE_SemiLattice : SemiLattice (SLo := СE_SemiLatticeOps) (Lo := СE_LeqOp).
Proof.
  refine {| PO_SemiLattice := СE_PartiallyOrdered |}.
  - intros x y; split; intro H.
    + apply sig_eq; exact (proj1 (leq_plus_def (ce_me x) (ce_me y)) H).
    + exact (proj2 (leq_plus_def (ce_me x) (ce_me y)) (f_equal ce_me H)).
  - intro x; apply sig_eq; exact (plus_neutral_left (ce_me x)).
  - intro x; apply sig_eq; exact (plus_idem (ce_me x)).
  - intros x y z; apply sig_eq; exact (plus_assoc (ce_me x) (ce_me y) (ce_me z)).
  - intros x y; apply sig_eq; exact (plus_com (ce_me x) (ce_me y)).
Qed.

Instance СE_LeftHandedIdemSemiRing :
    LeftHandedIdemSemiRing (Mo := СE_MonoidOps) (SLo := СE_SemiLatticeOps) (Lo := СE_LeqOp).
Proof.
  refine {| LHISR_Monoid := СE_Monoid; LHISR_SemiLattice := СE_SemiLattice |}.
  - intro x; apply sig_eq; exact (dot_ann_left (ce_me x)).
  - intros x y z; apply sig_eq; exact (dot_distr_left (ce_me x) (ce_me y) (ce_me z)).
  - intros x y z; exact (dot_distr_leq_right (ce_me x) (ce_me y) (ce_me z)).
Qed.

Instance СE_LeftHandedKleneeAlgebra :
    LeftHandedKleneeAlgebra (Mo := СE_MonoidOps) (SLo := СE_SemiLatticeOps)
                            (So := СE_StarOp) (Lo := СE_LeqOp).
Proof.
  refine {| LHKA_LHISR := СE_LeftHandedIdemSemiRing |}.
  - intro x; apply sig_eq; exact (star_make_right (ce_me x)).
  - intros a b H; exact (star_destruct_left (ce_me a) (ce_me b) H).
Qed.

Instance СE_IdemSemiRing :
    IdemSemiRing (Mo := СE_MonoidOps) (SLo := СE_SemiLatticeOps) (Lo := СE_LeqOp).
Proof.
  refine {| ISR_LHISR := СE_LeftHandedIdemSemiRing |}.
  - intro x; apply ce_eq; exact (endo_dot_ann_right (ce_fn x) (ce_cont x)).
  - intros z x y; apply ce_eq;
      exact (endo_dot_distr_right (ce_fn z) (ce_cont z) (ce_fn x) (ce_fn y)).
Qed.

Instance CE_KleeneAlgebra :
    KleeneAlgebra (Mo := СE_MonoidOps) (SLo := СE_SemiLatticeOps)
                  (So := СE_StarOp) (Lo := СE_LeqOp).
Proof.
  refine {| KA_LHKA := СE_LeftHandedKleneeAlgebra; KA_ISR := СE_IdemSemiRing |}.
  - intro x; apply ce_eq; exact (endo_star_make_left (ce_fn x) (ce_cont x) (ce_mono x)).
  - intros a b H; exact (endo_star_destruct_right (ce_fn a) (ce_fn b)
                           (ce_cont a) (ce_mono a) (ce_cont b) H).
Qed.
