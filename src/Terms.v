From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.btauto.Btauto.

Declare Scope term_scope.
Local Open Scope term_scope.

Delimit Scope term_scope with ATerm.

Section TermSyntax.
  Context {A : Type}.

  Inductive ATerm :=
  | letter : A -> ATerm
  | zero : ATerm
  | one : ATerm
  | plus : ATerm -> ATerm -> ATerm
  | dot : ATerm -> ATerm -> ATerm
  | star : ATerm -> ATerm
  | dual : ATerm -> ATerm
  .

  Inductive NoDual : ATerm -> Prop :=
  | N_letter : forall a, NoDual (letter a)
  | N_zero : NoDual zero
  | N_one : NoDual one
  | N_plus : forall t1 t2, NoDual t1 -> NoDual t2 -> NoDual (plus t1 t2)
  | N_dot : forall t1 t2, NoDual t1 -> NoDual t2 -> NoDual (dot t1 t2)
  | N_star : forall t, NoDual t -> NoDual (star t)
  .

  Definition NTerm := { t : ATerm | NoDual t }.

  Derive NoConfusion for ATerm.
End TermSyntax.

(* TODO: implement Ops typeclasses *)
Notation "0" := zero : term_scope.
Notation "1" := one : term_scope.
Notation "t1 + t2" := (plus t1 t2) (at level 50, left associativity) : term_scope.
Notation "t1 * t2" := (dot t1 t2) (at level 40, left associativity) : term_scope.
Notation "t #" := (star t) (at level 15, left associativity) : term_scope.
Notation "t ~" := (dual t) (at level 15, left associativity) : term_scope.

Section TermEquivalence.
  Context {A : Type}.

  Reserved Notation "t1 == t2" (at level 70) .
  Reserved Notation "t1 <= t2" (at level 70).

  Inductive term_equiv: @ATerm A -> @ATerm A -> Prop :=
  | ERefl: forall t, t == t
  | ESym: forall t1 t2, t1 == t2 -> t2 == t1
  | ETrans: forall t1 t2 t3, t1 == t2 -> t2 == t3 -> t1 == t3
  | ECongPlus: forall t1 t2 t3 t4, t1 == t2 -> t3 == t4 -> t1 + t3 == t2 + t4
  | ECongDot: forall t1 t2 t3 t4, t1 == t2 -> t3 == t4 -> t1 * t3 == t2 * t4
  | ECongStar: forall t1 t2, t1 == t2 -> t1# == t2#
  | ECongDual: forall t1 t2, t1 == t2 -> t1~ == t2~
  | EPlusIdemp: forall t, t + t == t
  | EPlusComm: forall t1 t2, t1 + t2 == t2 + t1
  | EPlusAssoc: forall t1 t2 t3, t1 + (t2 + t3) == (t1 + t2) + t3
  | EPlusUnit: forall t, t + 0 == t
  | EDotAssoc: forall t1 t2 t3, t1 * (t2 * t3) == (t1 * t2) * t3
  | EDotUnitRight: forall t, t * 1 == t
  | EDotUnitLeft: forall t, 1 * t == t
  | EDotZeroLeft: forall t, 0 * t == 0
  | EDistributeLeft: forall t1 t2 t3, (t1 + t2) * t3 == t1 * t3 + t2 * t3
  | EStarLeft: forall t, t# == t * t# + 1
  | EFixLeft: forall t1 t2, t1 * t2 <= t2 ->  t1# * t2 <= t2
  | EDualInvol: forall (t : @ATerm A), t ~ ~ == t
  | EDualAntitone: forall (t1 t2 : @ATerm A), t1 <= t2 -> t2 ~ <= t1 ~
  | EDualDot: forall (t1 t2 : @ATerm A), (t1 * t2) ~ == t1 ~ * t2 ~
  | EDualZero: forall (t : @ATerm A), t ~ * 0 + t * 0 ~ == 0 ~
  where "t1 == t2" := (term_equiv t1 t2) : term_scope
    and "t1 <= t2" := (t1 + t2 == t2) : term_scope.

  Global Add Relation (@ATerm A) term_equiv
    reflexivity proved by ERefl
    symmetry proved by ESym
    transitivity proved by ETrans
    as equiv_eq
  .

  Global Add Morphism plus
    with signature term_equiv ==> term_equiv ==> term_equiv
    as plus_mor
  .
  Proof.
    intros.
    now apply ECongPlus.
  Qed.

  Global Add Morphism dot
    with signature term_equiv ==> term_equiv ==> term_equiv
    as dot_mor
  .
  Proof.
    intros.
    now apply ECongDot.
  Qed.

  Global Add Morphism star
    with signature term_equiv ==> term_equiv
    as star_mor
  .
  Proof.
    intros.
    now apply ECongStar.
  Qed.

  Global Add Morphism dual
    with signature term_equiv ==> term_equiv
    as dual_mor
  .
  Proof.
    intros.
    now apply ECongDual.
  Qed.

  Definition term_lequiv (t1 t2: @ATerm A) := t1 <= t2.

  Lemma term_lequiv_refl (t: @ATerm A):
    t <= t
  .
  Proof.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_trans (t1 t2 t3: @ATerm A):
    t1 <= t2 -> t2 <= t3 -> t1 <= t3
  .
  Proof.
    intros.
    rewrite <- H0.
    rewrite <- H.
    repeat rewrite EPlusAssoc.
    rewrite EPlusIdemp.
    reflexivity.
  Qed.

  Lemma term_lequiv_zero (t: @ATerm A):
    0 <= t
  .
  Proof.
    now rewrite EPlusComm, EPlusUnit.
  Qed.

  Global Add Relation (@ATerm A) term_lequiv
    reflexivity proved by term_lequiv_refl
    transitivity proved by term_lequiv_trans
    as term_lequiv_po
  .

  Global Instance term_equiv_implies_lequiv: subrelation term_equiv term_lequiv.
  Proof.
    unfold subrelation, term_lequiv; intros.
    rewrite H.
    now rewrite EPlusIdemp.
  Qed.
End TermEquivalence.

Notation "t1 == t2" := (term_equiv t1 t2) (at level 70).
Notation "t1 <= t2" := (t1 + t2 == t2) (at level 70).

Ltac fold_term_lequiv :=
  match goal with
  | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
  end
.

Section TermProperties.
  Context {A : Type}.

  Lemma term_lequiv_split_left
    (t1 t2 t3: @ATerm A)
  :
    t1 <= t2 -> t1 <= t2 + t3
  .
  Proof.
    intros.
    rewrite <- H.
    repeat rewrite EPlusAssoc.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_split_right
    (t1 t2 t3: @ATerm A)
  :
    t1 <= t3 -> t1 <= t2 + t3
  .
  Proof.
    intros.
    rewrite <- H.
    rewrite EPlusAssoc with (t1 := t2).
    rewrite EPlusComm with (t1 := t2).
    repeat rewrite EPlusAssoc.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_split
    (t1 t2 t3: @ATerm A)
  :
    t1 <= t3 -> t2 <= t3 -> t1 + t2 <= t3
  .
  Proof.
    intros.
    rewrite <- H, <- H0.
    rewrite EPlusAssoc with (t1 := t1).
    rewrite EPlusAssoc with (t1 := (t1 + t2)).
    now rewrite EPlusIdemp.
  Qed.

  Global Add Morphism plus
    with signature term_lequiv ==> term_lequiv ==> (@term_lequiv A)
    as plus_mor_mono
  .
  Proof.
    unfold term_lequiv; intros.
    apply term_lequiv_split.
    - rewrite <- H.
      repeat apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - rewrite <- H0.
      apply term_lequiv_split_right.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
  Qed.

  Lemma term_lequiv_squeeze
    (t1 t2: @ATerm A)
  :
    t1 <= t2 ->
    t2 <= t1 ->
    t1 == t2
  .
  Proof.
    intros.
    rewrite <- H.
    rewrite <- H0 at 1.
    rewrite EPlusComm.
    reflexivity.
  Qed.
End TermProperties.

Section TermSum.
  Context {A : Type}.

  Equations sum (l: list (@ATerm A)): @ATerm A := {
    sum nil := 0;
    sum (t :: l) := t + sum l;
  }.

  Lemma sum_split (l1 l2: list (@ATerm A)):
    sum (l1 ++ l2) == sum l1 + sum l2
  .
  Proof.
    revert l2; induction l1; intros.
    - autorewrite with sum.
      now rewrite EPlusComm, EPlusUnit, app_nil_l.
    - rewrite <- app_comm_cons.
      autorewrite with sum.
      rewrite <- EPlusAssoc.
      now rewrite IHl1.
  Qed.

  Lemma sum_distribute_right (l: list (@ATerm A)) (t: @ATerm A):
    sum (map (fun x => x * t) l) == sum l * t
  .
  Proof.
    induction l; simpl; autorewrite with sum.
    - now rewrite EDotZeroLeft.
    - rewrite IHl.
      now rewrite EDistributeLeft.
  Qed.

  Lemma sum_lequiv_member
    (t: @ATerm A)
    (l: list (@ATerm A))
  :
    In t l ->
    t <= sum l
  .
  Proof.
    intros; induction l; destruct H.
    - subst.
      autorewrite with sum.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - autorewrite with sum.
      apply term_lequiv_split_right.
      now apply IHl.
  Qed.

  Lemma sum_lequiv_all
    (l: list (@ATerm A))
    (t: @ATerm A)
  :
    (forall (t': @ATerm A), In t' l -> t' <= t) ->
    sum l <= t
  .
  Proof.
    intros.
    induction l.
    - autorewrite with sum.
      apply term_lequiv_zero.
    - autorewrite with sum.
      apply term_lequiv_split.
      + apply H.
        now left.
      + apply IHl; intros.
        apply H.
        now right.
  Qed.

  Lemma sum_lequiv_containment
    (l1 l2: list (@ATerm A))
  :
    incl l1 l2 ->
    sum l1 <= sum l2
  .
  Proof.
    intros.
    apply sum_lequiv_all; intros.
    apply sum_lequiv_member.
    now apply H.
  Qed.

  Lemma sum_equiv_containment
    (l1 l2: list (@ATerm A))
  :
    incl l1 l2 ->
    incl l2 l1 ->
    sum l1 == sum l2
  .
  Proof.
    intros.
    apply term_lequiv_squeeze;
    now apply sum_lequiv_containment.
  Qed.
End TermSum.
