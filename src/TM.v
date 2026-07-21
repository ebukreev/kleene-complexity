Set Warnings "-stdlib-vector".
From Coq Require Import Lists.List Vectors.Vector Vectors.Fin.
Import ListNotations.
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

    Definition get_input_symbol (c : Conf) : option Σ :=
        nth_error (input c) (input_index c).

    Record TransitionCond := {
        input_symbol : Σ;
        work_tapes_symbols : Vector.t Γ work_tapes_num;
    }.

    Inductive Move := Left | Right | Stay. 

    Record TransitionAction := {
        new_work_tapes_symbols : Vector.t Γ work_tapes_num;
        input_move : Move;
        work_tapes_moves : Vector.t Move work_tapes_num;
    }.

    Definition update_index (idx : nat) (move : Move) : nat :=
        match move with
        | Left => 
            match idx with
            | 0 => 0
            | S n => n
            end
        | Right => S idx
        | Stay => idx
        end.

    Definition update_tape (tape : list Γ) (idx : nat) (new_sym : Γ) : list Γ :=
        (fix replace_nth (l : list Γ) (n : nat) (x : Γ) : list Γ :=
            match l, n with
            | [], _ => []
            | h :: t, 0 => x :: t
            | h :: t, S n' => h :: replace_nth t n' x
            end) tape idx new_sym.
    
    Definition work_tapes_consistent
        (c1 c2 : Conf) 
        (cond : TransitionCond) 
        (action : TransitionAction) : Prop :=
            forall (i : nat) (H : i < work_tapes_num),
                let fin_idx := of_nat_lt H in

                let tape1 := Vector.nth (work_tapes c1) fin_idx in
                let idx1 := Vector.nth (work_tapes_indices c1) fin_idx in
                let exp_sym := Vector.nth (work_tapes_symbols cond) fin_idx in
                let tape2 := Vector.nth (work_tapes c2) fin_idx in
                let idx2 := Vector.nth (work_tapes_indices c2) fin_idx in
                let new_sym := Vector.nth (new_work_tapes_symbols action) fin_idx in
                let mv := Vector.nth (work_tapes_moves action) fin_idx in
                
                (nth_error tape1 idx1 = Some exp_sym) /\
                (tape2 = update_tape tape1 idx1 new_sym) /\
                (idx2 = update_index idx1 mv).
    

    Record P := {
        t_cond : TransitionCond;
        t_action: TransitionAction;
    }.

    Class TM := {
        init : Q;
        final : Q -> bool;

        exist_transition : P -> Conf -> Conf -> Prop;
    }.

    Definition DTransitions := Q * TransitionCond -> Q * TransitionAction.

    Record DTM := {
        d_init : Q;
        d_final : Q -> bool;

        d_transitions : DTransitions;
    }.

    Definition exist_d_transition (d_transitions : DTransitions) (p : P) (c1 c2 : Conf) := 
        let (cond, action) := p in
        let (expected_new_state, expected_action) := d_transitions (state c1, cond) in
        
        (get_input_symbol c1 = Some (input_symbol cond)) /\
        (expected_action = action) /\
        (expected_new_state = state c2) /\
        (input c2 = input c1) /\
        (input_index c2 = update_index (input_index c1) (input_move action)) /\
        (work_tapes_consistent c1 c2 cond action).

    Global Instance DTM_TM (dtm : DTM) : TM :=
    {|
        init := d_init dtm;
        final := d_final dtm;

        exist_transition := exist_d_transition (d_transitions dtm);
    |}.

    Definition NTransitions := Q * TransitionCond -> list (Q * TransitionAction).

    Record NTM := {
        n_init : Q;
        n_final : Q -> bool;

        n_transitions : NTransitions;
    }.

    Definition exist_n_transition (n_transitions : NTransitions) (p : P) (c1 c2 : Conf) := 
        let (cond, action) := p in
        let possible_transitions := n_transitions (state c1, cond) in
        
        (get_input_symbol c1 = Some (input_symbol cond)) /\
        (exists (expected_state : Q) (expected_action : TransitionAction),
            List.In (expected_state, expected_action) possible_transitions /\
            expected_action = action /\
            expected_state = state c2) /\
        (input c2 = input c1) /\
        (input_index c2 = update_index (input_index c1) (input_move action)) /\
        (work_tapes_consistent c1 c2 cond action).

    Global Instance NTM_TM (ntm : NTM) : TM :=
    {|
        init := n_init ntm;
        final := n_final ntm;

        exist_transition := exist_n_transition (n_transitions ntm);
    |}.

    Inductive QType := Existential | Universal.

    Record ATM := {
        a_init : Q;
        a_final : Q -> bool;

        q_type : Q -> QType;
        a_transitions : NTransitions;
    }.

    Global Instance ATM_TM (atm : ATM) : TM :=
    {|
        init := a_init atm;
        final := a_final atm;

        exist_transition := exist_n_transition (a_transitions atm);
    |}.
End TuringMachines.

Definition transition `{TMParams} (tm : TM) (p : P) (conf1 conf2 : Conf) : Prop :=
    exist_transition p conf1 conf2.

Notation "conf1 ○ p ⊢ᶜ conf2" := (transition _ p conf1 conf2) (at level 70).

Definition Trace `{TM} := 
    { t : NEList Conf |
        let confs := toList t in
        (fix check_confs (cs : list Conf) (prev : option Conf) : Prop :=
            match cs, prev with
            | [], _ => True
            | c :: rest, None => check_confs rest (Some c)
            | c :: rest, Some prev_c =>
                exists (p : P), prev_c ○ p ⊢ᶜ c /\
                check_confs rest (Some c)
            end) confs None }.

Definition ttransition `{TMParams} (tm : TM) (p : P) (trace1 trace2 : Trace) : Prop :=
    match trace1, trace2 with
    | exist _ t1 _, exist _ t2 _ =>
        let head1 := head t1 in
        let head2 := head t2 in
            t2 = cons head2 (t1) /\
            head1 ○ p ⊢ᶜ head2
    end.

Notation "trace1 ○ p ⊢ trace2" := (ttransition _ p trace1 trace2) (at level 70).
