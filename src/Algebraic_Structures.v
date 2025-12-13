From Coq Require Import Sets.Powerset.

Section Ops.

    Class Monoid_Ops (A : Type) := {
        one : A;
        dot : A -> A -> A;    
    }.

    Class SemiLattice_Ops (A : Type) := {
        zero : A;
        plus : A -> A -> A;
    }.

    Class Leq_Op (A : Type) := {
        leq : A -> A -> Prop;
    }.

    Class Star_Op (A : Type) := {
        star: A -> A
    }.

    Class Complement_Op (A : Type) := {
        comp : A -> A;
    }.

End Ops.

Notation "x <== y" := (leq x y) (at level 70). 
Notation "x * y" := (dot x y) (at level 40, left associativity). 
Notation "x + y" := (plus x y) (at level 50, left associativity). 
Notation "x #"   := (star x) (at level 15, left associativity).
Notation "! x" := (comp x) (at level 35, right associativity).
Notation "1" := one.
Notation "0" := zero.

Section Structures.

    Context {A : Type}.

    Class Monoid {Mo : Monoid_Ops A} := {
        dot_assoc : forall x y z, x*(y*z) = (x*y)*z;
        dot_neutral_left : forall x, 1*x = x;
        dot_neutral_right : forall x, x*1 = x;
    }.

    Class PartiallyOrdered {Lo : Leq_Op A} := {
        leq_refl : forall x, x <== x;
        leq_antisym : forall x y, x <== y -> y <== x -> x = y;
        leq_trans : forall x y z, x <== y -> y <== z -> x <== z
    }.

    Class SemiLattice {SLo : SemiLattice_Ops A} {Lo : Leq_Op A} := {
        PO_SemiLattice :: PartiallyOrdered;
        leq_plus_def: forall x y, x <== y <-> x + y = y;
        plus_neutral_left: forall x, 0+x = x;
        plus_idem: forall x, x+x = x;
        plus_assoc: forall x y z, x+(y+z) = (x+y)+z;
        plus_com: forall x y, x+y = y+x
    }.

    Class LeftHandedIdemSemiRing {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {Lo : Leq_Op A} := {
        LHISR_Monoid :: Monoid;
        LHISR_SemiLattice :: SemiLattice;
        dot_ann_left:  forall x, 0 * x = 0;
        dot_distr_left:  forall x y z, (x+y)*z = x*z + y*z;
        dot_distr_leq_right: forall x y z, z*x + z*y <== z*(x+y)
    }.

    Class IdemSemiRing {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {Lo : Leq_Op A} := {
        ISR_LHISR :: LeftHandedIdemSemiRing;
        dot_ann_right: forall x, x * 0 = 0;
        dot_distr_right: forall z x y, z*(x+y) = z*x + z*y
    }.

    Class LeftHandedKleneeAlgebra {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {So : Star_Op A} {Lo : Leq_Op A} := {
        LHKA_LHISR :: LeftHandedIdemSemiRing;
        star_make_right: forall x, 1 + x*x# = x#;
        star_destruct_left: forall a b, a*b <== b  ->  a#*b <== b;
    }.

    Class KleeneAlgebra {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {So : Star_Op A} {Lo : Leq_Op A} := {
        KA_LHKA :: LeftHandedKleneeAlgebra;
        star_make_left: forall x, 1 + x#*x = x#;
        star_destruct_right: forall a b, b*a <== b  ->  b*a# <== b
    }.    

    Class BooleanAlgebra {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {Co : Complement_Op A} {Lo : Leq_Op A} := {
        BA_Monoid :: Monoid;
        BA_SemiLattice :: SemiLattice;
        dot_comm : forall x y, x * y = y * x;
        dot_idem : forall x, x * x = x;
        distr_dot_plus : forall x y z, x * (y + z) = (x * y) + (x * z);
        distr_plus_dot : forall x y z, x + (y * z) = (x + y) * (x + z);
        comp_non_contradiction : forall x, x * !x = 0;
        comp_excluded_middle : forall x, x + !x = 1; 
    }.

    Definition UpperBound {Lo : Leq_Op A} (X : Ensemble A) (u : A) : Prop :=
        forall x, In _ X x -> x <== u.
    
    Definition LowerBound {Lo : Leq_Op A} (X : Ensemble A) (l : A) : Prop :=
        forall x, In _ X x -> l <== x.
    
    Definition LUB {Lo : Leq_Op A} (X : Ensemble A) (lub : A) : Prop :=
        UpperBound X lub /\ forall u, UpperBound X u -> lub <== u.
    
    Definition GLB {Lo : Leq_Op A} (X : Ensemble A) (glb : A) : Prop :=
        LowerBound X glb /\ forall l, LowerBound X l -> l <== glb.
    
    Class CompleteLattice {Lo : Leq_Op A} := {
        PO_CompleteLattice :: PartiallyOrdered;

        sup : Ensemble A -> A;
        sup_is_lub : forall X, LUB X (sup X);
  
        inf : Ensemble A -> A;
        inf_is_glb : forall X, GLB X (inf X);
    }.
    
End Structures.
