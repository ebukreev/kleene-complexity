From klenee_complexity Require Import Algebraic_Structures Conf.
From Coq Require Import Strings.String Logic.Classical Sets.Powerset Logic.FunctionalExtensionality Sets.Constructive_sets.

Definition Domain := string -> Ensemble Trace.

Instance Domain_MonoidOps : Monoid_Ops Domain := {
    one := fun _ => Full_set Trace;
    dot a b := fun i => Intersection Trace (a i) (b i)
}.

Lemma dot_assoc_domain : forall (x y z : Domain),
    x * (y * z) = (x * y) * z.
Proof.
  intros x y z.
  extensionality i.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; unfold Included; intros t H.
  - inversion H as [t' H1 H2].
    inversion H2 as [t'' H3 H4].
    constructor.
    + constructor; assumption.
    + assumption.
  - inversion H as [t' H1 H2].
    inversion H1 as [t'' H3 H4].
    constructor.
    + assumption.
    + constructor; assumption.
Qed.

Lemma dot_neutral_left_domain : forall (x : Domain),
    1 * x = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; unfold Included; intros t H.
  - inversion H as [t' H1 H2].
    assumption.
  - constructor.
    + constructor.
    + assumption.
Qed.

Lemma dot_neutral_right_domain : forall (x : Domain),
    x * 1 = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; unfold Included; intros t H.
  - inversion H as [t' H1 H2].
    assumption.
  - constructor.
    + assumption.
    + constructor.
Qed.

Instance Domain_Monoid : Monoid (Mo := Domain_MonoidOps) := {
    dot_assoc := dot_assoc_domain;
    dot_neutral_left := dot_neutral_left_domain;
    dot_neutral_right := dot_neutral_right_domain
}.

Instance Domain_SemiLatticeOps : SemiLattice_Ops Domain := {
    zero := fun _ => Empty_set Trace;
    plus a b := fun i => Union Trace (a i) (b i)
}.

Instance Domain_LeqOp : Leq_Op Domain := {
    leq a b := forall i, Included Trace (a i) (b i)
}.

Lemma domain_leq_refl : forall (x : Domain), x <== x.
Proof.
  intros x i.
  red. intros t H. assumption.
Qed.

Lemma domain_leq_antisym : forall (x y : Domain), 
    x <== y -> y <== x -> x = y.
Proof.
  intros x y Hxy Hyx.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red. intros t H. apply (Hxy i). assumption.
  - red. intros t H. apply (Hyx i). assumption.
Qed.

Lemma domain_leq_trans : forall (x y z : Domain), 
    x <== y -> y <== z -> x <== z.
Proof.
  intros x y z Hxy Hyz i.
  red. intros t H.
  apply (Hyz i).
  apply (Hxy i).
  assumption.
Qed.

Instance Domain_PartiallyOrdered : PartiallyOrdered (Lo := Domain_LeqOp) := {
    leq_refl := domain_leq_refl;
    leq_antisym := domain_leq_antisym;
    leq_trans := domain_leq_trans
}.

Lemma domain_leq_plus_def : forall (x y : Domain), 
    x <== y <-> x + y = y.
Proof.
  intros x y.
  split.
  - intro H.
    extensionality i.
    apply Extensionality_Ensembles.
    split.
    + intros t H1. inversion H1; [apply (H i) | idtac]; assumption.
    + intros t H1. apply Union_intror; assumption.
  - intro H.
    intros i t H1.
    assert (H2 : plus x y i = y i) by (rewrite H; reflexivity).
    simpl in H2.
    pose proof (Union_introl Trace (x i) (y i) t H1).
    rewrite H2 in H0.
    assumption.
Qed.

Lemma domain_plus_neutral_left : forall (x : Domain), 
    0 + x = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    inversion H; [inversion H0 | assumption].
  - red; intros t H.
    apply Union_intror; assumption.
Qed.

Lemma domain_plus_idem : forall (x : Domain), 
    x + x = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    inversion H; assumption.
  - red; intros t H.
    apply Union_introl; assumption.
Qed.

Lemma domain_plus_assoc : forall (x y z : Domain), 
    x + (y + z) = (x + y) + z.
Proof.
  intros x y z.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    destruct H as [t H1 | t H1].
    + apply Union_introl.
      apply Union_introl.
      assumption.
    + destruct H1 as [t H2 | t H2].
      * apply Union_introl.
        apply Union_intror.
        assumption.
      * apply Union_intror.
        assumption.
  - red; intros t H.
    destruct H as [t H1 | t H1].
    + destruct H1 as [t H2 | t H2].
      * apply Union_introl.
        assumption.
      * apply Union_intror.
        apply Union_introl.
        assumption.
    + apply Union_intror.
      apply Union_intror.
      assumption.
Qed.

Lemma domain_plus_com : forall (x y : Domain), 
    x + y = y + x.
Proof.
  intros x y.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    inversion H; [apply Union_intror | apply Union_introl]; assumption.
  - red; intros t H.
    inversion H; [apply Union_intror | apply Union_introl]; assumption.
Qed.

Lemma domain_plus_monotone_left : forall x y z,
  x <== y -> z + x <== z + y.
Proof.
  intros x y z H.
  apply domain_leq_plus_def.
  rewrite domain_leq_plus_def in H.
  rewrite domain_plus_assoc.
  rewrite (domain_plus_com (z + x) z).
  rewrite domain_plus_assoc.
  rewrite domain_plus_idem.
  rewrite <- domain_plus_assoc.
  rewrite H.
  reflexivity.
Qed.

Lemma domain_plus_is_lub : forall x y z,
  x <== z -> y <== z -> x + y <== z.
Proof.
  intros x y z H1 H2.
  apply domain_leq_plus_def.
  rewrite domain_leq_plus_def in H1.
  rewrite domain_leq_plus_def in H2.
  rewrite <- domain_plus_assoc.
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

Instance Domain_SemiLattice : SemiLattice (SLo := Domain_SemiLatticeOps) (Lo := Domain_LeqOp) := {
    PO_SemiLattice := Domain_PartiallyOrdered;
    leq_plus_def := domain_leq_plus_def;
    plus_neutral_left := domain_plus_neutral_left;
    plus_idem := domain_plus_idem;
    plus_assoc := domain_plus_assoc;
    plus_com := domain_plus_com
}.

Instance Domain_ComplementOp : Complement_Op Domain := {
    comp a := fun i => Setminus Trace (Full_set Trace) (a i)
}.

Lemma domain_dot_comm : forall (x y : Domain), x * y = y * x.
Proof.
  intros x y.
  extensionality i.
  apply Extensionality_Ensembles.
  split; red; intros t H;
  inversion H; constructor; assumption.
Qed.

Lemma domain_dot_idem : forall (x : Domain), x * x = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H. inversion H; assumption.
  - red; intros t H. constructor; assumption.
Qed.

Lemma domain_distr_dot_plus : forall (x y z : Domain), 
    x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    inversion H as [t' H1 H2].
    inversion H2 as [t'' H3 | t'' H3].
    + left; constructor; assumption.
    + right; constructor; assumption.
  - red; intros t H.
    inversion H as [t' H1 | t' H1].
    + inversion H1 as [t'' H2 H3].
      constructor; [assumption | left; assumption].
    + inversion H1 as [t'' H2 H3].
      constructor; [assumption | right; assumption].
Qed.

Lemma domain_distr_plus_dot : forall (x y z : Domain), 
    x + (y * z) = (x + y) * (x + z).
Proof.
  intros x y z.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - red; intros t H.
    inversion H as [t' H1 | t' H1].
    + constructor.
      * left; assumption.
      * left; assumption.
    + inversion H1 as [t'' H2 H3].
      constructor.
      * right; assumption.
      * right; assumption.
  - red; intros t H.
    inversion H as [t' H1 H2].
    inversion H1 as [t'' H3 | t'' H3];
    inversion H2 as [t''' H5 | t''' H5].
    + left; assumption.
    + left; assumption.
    + left; assumption.
    + right; constructor; assumption.
Qed.

Lemma domain_comp_non_contradiction : forall (x : Domain), 
    x * !x = 0.
Proof.
  intros x.
  extensionality i.
  unfold Setminus.
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    destruct H as [t H1 H2].
    destruct H2 as [H2 H3].
    contradiction.
  - intros t H.
    inversion H.
Qed.

Lemma domain_comp_excluded_middle : forall (x : Domain), 
    x + !x = 1.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H.
    destruct H as [t H | t H].
    + apply Full_intro.
    + destruct H as [H _]; apply Full_intro.
  - intros t H.
  destruct (classic (In Trace (x i) t)) as [H_in | H_not_in].
  + left; exact H_in.
  + right; constructor; [apply Full_intro | exact H_not_in].
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
Proof.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H. destruct H as [l [l' r]]. contradiction. 
  - intros t H. contradiction.
Qed.

Lemma domain_lub_singleton : forall x, domain_lub (Singleton Domain x) = x.
Proof.
  intros x.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H. destruct H as [h [l r]]. apply Singleton_inv in l.
    rewrite <- l in r.
    assumption.
  - intros t H.
    exists x.
    split.
    + reflexivity.
    + assumption.
Qed.

Lemma domain_lub_union : forall A B, 
  domain_lub (Union Domain A B) = (domain_lub A) + (domain_lub B).
Proof.
  intros A B.
  extensionality i.
  apply Extensionality_Ensembles.
  split.
  - intros t H. destruct H.
    destruct H as [H_union H_trace].
    destruct H_union as [x_in_A | x_in_B].
    + left.
      exists x_in_A.
      split; assumption.
    + right.
      exists x_in_B.
      split; assumption.
  - red. intros. red in H. red.  
    destruct H as [x H | x H].
    + destruct H as [d [H_A H_trace]].
      exists d.
      split.
      ++ left; assumption.
      ++ assumption.
    + destruct H as [d [H_B H_trace]].
      exists d.
      split.
    ++ right; assumption.
    ++ assumption.
Qed.
