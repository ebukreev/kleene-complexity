Set Warnings "-stdlib-vector".
From Coq Require Vectors.Vector.
From klenee_complexity Require Import NEList.

Section TuringMachines.
    Class TMParams := {
        Q : Type;
        Σ : Type;
        Γ : Type;
        work_tapes_num : nat;
    }.

    Context `{params : TMParams}.

    Record Conf := {
        state : Q;
        input : list Σ;
        input_index : nat;
        work_tapes : Vector.t (list Γ) work_tapes_num;
        work_tapes_indices : Vector.t nat work_tapes_num;
    }.

    Definition Trace  := NEList Conf.

    Class TM := {
        init : Q;
        final : Q -> bool;

        transitions : Type;
        do_transition : Conf -> Conf;
    }.

    Record DTM := {
        d_init : Q;
        d_final : Q -> bool;
    }.

    Inductive Move := Left | Right | Stay. 

    Definition DTransitions (n : nat) :=
        Q * Σ * (Vector.t Γ n) -> 
        Q * (Vector.t Γ n) * Move * (Vector.t Move n).

    Global Instance DTM_TM (dtm : DTM) : TM :=
    {|
        init := d_init dtm;
        final := d_final dtm;

        transitions := DTransitions work_tapes_num;
        do_transition := id; (*TODO*)
    |}.

    Record NTM := {
        n_init : Q;
        n_final : Q -> bool;
    }.

    Definition NTransitions (n : nat) :=
        Q * Σ * (Vector.t Γ n) -> 
        list (Q * (Vector.t Γ n) * Move * (Vector.t Move n)).

    Global Instance NTM_TM (ntm : NTM) : TM :=
    {|
        init := n_init ntm;
        final := n_final ntm;

        transitions := NTransitions work_tapes_num;
        do_transition := id; (*TODO*)
    |}.

    Inductive QType := Existential | Universal.

    Record ATM := {
        a_init : Q;
        a_final : Q -> bool;

        q_type : Q -> QType;
    }.

    Global Instance ATM_TM (atm : ATM) : TM :=
    {|
        init := a_init atm;
        final := a_final atm;

        transitions := NTransitions work_tapes_num;
        do_transition := id; (*TODO*)
    |}.
End TuringMachines.

Definition transition `{TMParams} (tm : TM) (conf1 conf2 : Conf) : Prop :=
    do_transition conf1 = conf2.

Notation "conf1 ⊢ᶜ conf2" := (transition _ conf1 conf2) (at level 70).

Definition ttransition `{TMParams} (tm : TM) (trace1 trace2 : Trace) : Prop :=
    let head1 := head trace1 in
    let head2 := head trace2 in
        trace2 = cons head2 (trace1) /\
        head1 ⊢ᶜ head2.

Notation "trace1 ⊢ trace2" := (ttransition _ trace1 trace2) (at level 70).
