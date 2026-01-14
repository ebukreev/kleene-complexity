From klenee_complexity Require Import Algebraic_Structures Domain TM.
From Coq Require Import Program.Basics.
From Coq Require Import Sets.Powerset Sets.Image.
From Coq Require Import Logic.FunctionalExtensionality.

Definition Monotone {A} {Lo : Leq_Op A} (F : A -> A) : Prop :=
    forall x y, x <== y -> F x <== F y.
    
Definition PreFixedPoint {A} {Lo : Leq_Op A} (F : A -> A) (x : A) : Prop :=
    F x <== x.
    
Definition PostFixedPoint {A} {Lo : Leq_Op A} (F : A -> A) (x : A) : Prop :=
    x <== F x.

Theorem Knaster_Tarski {A} {Lo : Leq_Op A} {CL : CompleteLattice}
        (F : A -> A) (F_mono : Monotone F) :
  exists lfp : A,
    F lfp = lfp /\ (forall x, F x = x -> lfp <== x).
Proof.
  set (P := fun x : A => F x <== x).
  set (p := inf P).
  
  assert (Hfp_le_p : F p <== p).
  {
    destruct (inf_is_glb P) as [Hp_lb Hp_glb].
    apply Hp_glb.
    
    intros x Hx_in_P.
    
    unfold P in Hx_in_P.
    
    assert (Hp_le_x : p <== x).
    { apply Hp_lb. exact Hx_in_P. }
    
    apply F_mono in Hp_le_x.
    apply (leq_trans (F p) (F x) x Hp_le_x).
    exact Hx_in_P.
  }
  
  assert (Hp_le_fp : p <== F p).
  {
    assert (HFp_in_P : In A P (F p)).
    {
      unfold P.
      apply F_mono in Hfp_le_p.
      assumption.
    }
    
    destruct (inf_is_glb P) as [Hp_l _].
    apply Hp_l.
    exact HFp_in_P.
  }
  
  assert (H_fp_eq : F p = p).
  { apply leq_antisym; assumption. }
  
  assert (H_least : forall x, F x = x -> p <== x).
  {
    intros x Hx.
    assert (Hx_in_P : In A P x).
    {
      unfold P.
      red.
      rewrite Hx.
      apply leq_refl.
    }
    
    destruct (inf_is_glb P) as [Hp_l _].
    apply Hp_l.
    exact Hx_in_P.
  }
  
  exists p.
  split; assumption.
Qed.

Definition lfp {A} {Lo : Leq_Op A} {CL : CompleteLattice}
               (F : A -> A) (F_mono : Monotone F) : A :=
        inf (fun x => F x <== x).

Lemma lfp_is_fixed_point {A} {Lo : Leq_Op A} {CL : CompleteLattice}
                (F : A -> A) (F_mono : Monotone F) :
        F (lfp F F_mono) = lfp F F_mono.
Proof.
  unfold lfp.
  set (P := fun x : A => F x <== x).
  set (p := inf P).
  assert (H_fp_eq : F p = p).
  {
    destruct (inf_is_glb P) as [Hp_lb Hp_glb].
    
    assert (Hfp_le_p : F p <== p).
    {
      apply Hp_glb.
      intros x Hx_in_P.
      unfold P in Hx_in_P.
      assert (Hp_le_x : p <== x) by (apply Hp_lb; exact Hx_in_P).
      apply F_mono in Hp_le_x.
      apply (leq_trans (F p) (F x) x Hp_le_x Hx_in_P).
    }
    
    assert (Hp_le_fp : p <== F p).
    {
      assert (HFp_in_P : In A P (F p)).
      {
        unfold P.
        apply F_mono in Hfp_le_p.
        exact Hfp_le_p.
      }
      apply Hp_lb.
      exact HFp_in_P.
    }
    
    apply leq_antisym; assumption.
  }
  exact H_fp_eq.
Qed.
    
Lemma lfp_is_least {A} {Lo : Leq_Op A} {CL : CompleteLattice}
                (F : A -> A) (F_mono : Monotone F) (x : A) :
        F x = x -> lfp F F_mono <== x.
Proof.
  intro H_fx_eq.
  unfold lfp.
  set (P := fun x : A => F x <== x).
  destruct (inf_is_glb P) as [H_lb _].
  
  assert (Hx_in_P : In A P x).
  {
    unfold P.
    red.
    rewrite H_fx_eq.
    apply leq_refl.
  }
  
  apply H_lb.
  exact Hx_in_P.
Qed.