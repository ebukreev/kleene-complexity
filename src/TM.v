From Coq Require Fin.
From klenee_complexity Require Import NEList.

Class TMParams := {
  Q : Type;
  Σ : Type;
  Γ : Type;
  work_tapes_num : nat;
}.

Section TuringMachines.
    Context `{TMParams}.

    Inductive Move := Left | Right | Stay. 

    Record TM (TransitionsFunc : nat -> Type) := {
        init : Q;
        final : Q -> bool;
        transitions : TransitionsFunc work_tapes_num;
    }.

    Definition DTransitions (n : nat) :=
        Q * Σ * (Fin.t n -> Γ) -> 
        Q * (Fin.t n -> Γ) * Move * (Fin.t n -> Move).

    Definition NTransitions (n : nat) :=
        Q * Σ * (Fin.t n -> Γ) -> 
        list (Q * (Fin.t n -> Γ) * Move * (Fin.t n -> Move)).

    Definition DTM := TM DTransitions.
    Definition NTM := TM NTransitions.

    Inductive QType := Existential | Universal.

    Record ATM := {
        ntm : NTM;
        q_type : Q -> QType;
    }.

    Record Conf := {
        state : Q;
        input : list Σ;
        input_index : nat;
        work_tapes : Fin.t work_tapes_num -> list Γ;
        work_tapes_indices : Fin.t work_tapes_num -> nat;
    }.

    Definition Trace := NEList Conf.

End TuringMachines.