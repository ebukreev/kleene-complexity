From klenee_complexity Require Import Algebraic_Structures Conf.
From Coq Require Import Strings.String Logic.Classical Sets.Powerset Logic.FunctionalExtensionality Sets.Constructive_sets.

Definition Domain := string -> Ensemble Trace.

Instance Domain_MonoidOps : Monoid_Ops Domain := {
    one := fun _ => Full_set Trace;
    dot a b := fun i => Intersection Trace (a i) (b i)
}.

Instance Domain_SemiLatticeOps : SemiLattice_Ops Domain := {
    zero := fun _ => Empty_set Trace;
    plus a b := fun i => Union Trace (a i) (b i)
}.

Instance Domain_LeqOp : Leq_Op Domain := {
    leq a b := forall i, Included Trace (a i) (b i)
}.

Instance Domain_ComplementOp : Complement_Op Domain := {
    comp a := fun i => Setminus Trace (Full_set Trace) (a i)
}.

Ltac ens_step :=
  match goal with
  | [ H : In _ _ _             |- _ ] => red in H
  | [ H : Union _ _ _ _        |- _ ] => destruct H
  | [ H : Intersection _ _ _ _ |- _ ] => destruct H
  | [ H : Setminus _ _ _ _     |- _ ] => destruct H
  | [ H : Empty_set _ _        |- _ ] => destruct H
  | [ |- In _ (Intersection _ _ _) _ ] => constructor
  | [ |- In _ (Setminus _ _ _) _     ] => constructor
  | [ |- In _ (Full_set _) _         ] => constructor
  end.

Ltac domain_ext :=
  extensionality i; apply Extensionality_Ensembles; split;
  intros t Ht; unfold Included in *; simpl in *;
  repeat ens_step; try contradiction; auto with sets.

Lemma dot_assoc_domain : forall (x y z : Domain),
    x * (y * z) = (x * y) * z.
Proof. intros x y z; domain_ext. Qed.

Lemma dot_neutral_left_domain : forall (x : Domain),
    1 * x = x.
Proof. intros x; domain_ext. Qed.

Lemma dot_neutral_right_domain : forall (x : Domain),
    x * 1 = x.
Proof. intros x; domain_ext. Qed.

Instance Domain_Monoid : Monoid (Mo := Domain_MonoidOps) := {
    dot_assoc := dot_assoc_domain;
    dot_neutral_left := dot_neutral_left_domain;
    dot_neutral_right := dot_neutral_right_domain
}.

Lemma domain_leq_refl : forall (x : Domain), x <== x.
Proof. intros x i t H; assumption. Qed.

Lemma domain_leq_antisym : forall (x y : Domain),
    x <== y -> y <== x -> x = y.
Proof.
  intros x y Hxy Hyx.
  extensionality i.
  apply Extensionality_Ensembles.
  split; [apply Hxy | apply Hyx].
Qed.

Lemma domain_leq_trans : forall (x y z : Domain),
    x <== y -> y <== z -> x <== z.
Proof.
  intros x y z Hxy Hyz i t H.
  apply (Hyz i), (Hxy i), H.
Qed.

Instance Domain_PartiallyOrdered : PartiallyOrdered (Lo := Domain_LeqOp) := {
    leq_refl := domain_leq_refl;
    leq_antisym := domain_leq_antisym;
    leq_trans := domain_leq_trans
}.

Lemma domain_leq_plus_def : forall (x y : Domain),
    x <== y <-> x + y = y.
Proof.
  intros x y; split.
  - intro H.
    extensionality i.
    apply Extensionality_Ensembles; split; intros t Ht.
    + destruct Ht as [t Ht | t Ht]; [apply (H i) | ]; exact Ht.
    + apply Union_intror, Ht.
  - intros H i t Ht.
    rewrite <- H.
    apply Union_introl, Ht.
Qed.

Lemma domain_plus_neutral_left : forall (x : Domain),
    0 + x = x.
Proof. intros x; domain_ext. Qed.

Lemma domain_plus_idem : forall (x : Domain),
    x + x = x.
Proof. intros x; domain_ext. Qed.

Lemma domain_plus_assoc : forall (x y z : Domain),
    x + (y + z) = (x + y) + z.
Proof. intros x y z; domain_ext. Qed.

Lemma domain_plus_com : forall (x y : Domain),
    x + y = y + x.
Proof. intros x y; domain_ext. Qed.

Lemma domain_plus_monotone_left : forall x y z,
  x <== y -> z + x <== z + y.
Proof.
  intros x y z H i t Ht.
  destruct Ht as [t Ht | t Ht].
  - apply Union_introl, Ht.
  - apply Union_intror, (H i), Ht.
Qed.

Lemma domain_plus_is_lub : forall x y z,
  x <== z -> y <== z -> x + y <== z.
Proof.
  intros x y z H1 H2 i t Ht.
  destruct Ht as [t Ht | t Ht]; [apply (H1 i) | apply (H2 i)]; exact Ht.
Qed.

Lemma domain_leq_plus_left : forall (x y : Domain), x <== x + y.
Proof.
  intros x y; apply domain_leq_plus_def.
  now rewrite domain_plus_assoc, domain_plus_idem.
Qed.

Lemma domain_leq_plus_right : forall (x y : Domain), y <== x + y.
Proof.
  intros x y; rewrite domain_plus_com; apply domain_leq_plus_left.
Qed.

Instance Domain_SemiLattice : SemiLattice (SLo := Domain_SemiLatticeOps) (Lo := Domain_LeqOp) := {
    PO_SemiLattice := Domain_PartiallyOrdered;
    leq_plus_def := domain_leq_plus_def;
    plus_neutral_left := domain_plus_neutral_left;
    plus_idem := domain_plus_idem;
    plus_assoc := domain_plus_assoc;
    plus_com := domain_plus_com
}.

Lemma domain_dot_comm : forall (x y : Domain), x * y = y * x.
Proof. intros x y; domain_ext. Qed.

Lemma domain_dot_idem : forall (x : Domain), x * x = x.
Proof. intros x; domain_ext. Qed.

Lemma domain_distr_dot_plus : forall (x y z : Domain),
    x * (y + z) = (x * y) + (x * z).
Proof. intros x y z; domain_ext. Qed.

Lemma domain_distr_plus_dot : forall (x y z : Domain),
    x + (y * z) = (x + y) * (x + z).
Proof. intros x y z; domain_ext. Qed.

Lemma domain_comp_non_contradiction : forall (x : Domain),
    x * !x = 0.
Proof. intros x; domain_ext. Qed.

Lemma domain_comp_excluded_middle : forall (x : Domain),
    x + !x = 1.
Proof.
  intros x; domain_ext.
  destruct (classic (In Trace (x i) t)); auto with sets.
Qed.

Instance Domain_BooleanAlgebra : BooleanAlgebra (Mo := Domain_MonoidOps) (SLo := Domain_SemiLatticeOps) (Co := Domain_ComplementOp) (Lo := Domain_LeqOp) := {
    BA_Monoid := Domain_Monoid;
    BA_SemiLattice := Domain_SemiLattice;
    dot_comm := domain_dot_comm;
    dot_idem := domain_dot_idem;
    distr_dot_plus := domain_distr_dot_plus;
    distr_plus_dot := domain_distr_plus_dot;
    comp_non_contradiction := domain_comp_non_contradiction;
    comp_excluded_middle := domain_comp_excluded_middle
}.

Definition domain_lub (X : Ensemble Domain) : Domain :=
  fun (i : string) (t : Trace) => exists x, In _ X x /\ In _ (x i) t.

Definition domain_glb (X : Ensemble Domain) : Domain :=
  fun (i : string) (t : Trace) => forall x, In _ X x -> In _ (x i) t.

Lemma Domain_sup_is_lub X : LUB X (domain_lub X).
Proof.
  constructor.
  - intros x Hx i t Ht; exists x; auto.
  - intros y Hy i t [x [Hx Ht]]; apply (Hy x Hx i); auto.
Qed.

Lemma Domain_inf_is_glb X : GLB X (domain_glb X).
Proof.
  constructor.
  - intros x Hx i t Ht; apply Ht; auto.
  - intros y Hy i t Ht x Hx; apply (Hy x Hx i); auto.
Qed.

Instance Domain_CompleteLattice : CompleteLattice (Lo := Domain_LeqOp) := {
  PO_CompleteLattice := Domain_PartiallyOrdered;
  sup := domain_lub;
  sup_is_lub := Domain_sup_is_lub;
  inf := domain_glb;
  inf_is_glb := Domain_inf_is_glb;
}.

Lemma domain_lub_empty : domain_lub (Empty_set Domain) = zero.
Proof. domain_ext; firstorder. Qed.

Lemma domain_lub_singleton : forall x, domain_lub (Singleton Domain x) = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - destruct Ht as [d [Hd Ht]].
    apply Singleton_inv in Hd; subst; assumption.
  - exists x; split; [constructor | assumption].
Qed.

Lemma domain_lub_union : forall A B,
  domain_lub (Union Domain A B) = (domain_lub A) + (domain_lub B).
Proof.
  intros A B.
  extensionality i.
  apply Extensionality_Ensembles; split; intros t Ht.
  - destruct Ht as [d [Hd Ht]].
    destruct Hd as [d Hd | d Hd]; [left | right]; exists d; auto.
  - destruct Ht as [t Ht | t Ht]; destruct Ht as [d [Hd Ht]];
      exists d; split; auto with sets.
Qed.
