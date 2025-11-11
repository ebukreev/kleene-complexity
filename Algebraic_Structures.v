Section Ops.

    Class Monoid_Ops (A : Type) := {
        one : A;
        dot : A -> A -> A;    
    }.

    Class SemiLattice_Ops (A : Type) := {
        zero : A;
        plus : A -> A -> A;
        leq : A -> A -> Prop;
    }.

    Class Star_Op (A : Type) := {
        star: A -> A
    }.

End Ops.

Notation "x <== y" := (leq x y) (at level 70). 
Notation "x * y" := (dot x y) (at level 40, left associativity). 
Notation "x + y" := (plus x y) (at level 50, left associativity). 
Notation "x #"   := (star x) (at level 15, left associativity).
Notation "1" := one.
Notation "0" := zero.

Section Structures.

    Context {A : Type}.

    Class Monoid {Mo : Monoid_Ops A} := {
        dot_assoc : forall x y z, x*(y*z) = (x*y)*z;
        dot_neutral_left : forall x, 1*x = x;
        dot_neutral_right : forall x, x*1 = x;
    }.

    Class SemiLattice {SLo : SemiLattice_Ops A} := {
        leq_plus_def : forall x y, x <== y <-> x + y = y;
        plus_neutral_left: forall x, 0+x = x;
        plus_idem: forall x, x+x = x;
        plus_assoc: forall x y z, x+(y+z) = (x+y)+z;
        plus_com: forall x y, x+y = y+x
    }.

    Class LeftHandedIdemSemiRing {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} := {
        LHISR_Monoid :: Monoid;
        LHISR_SemiLattice :: SemiLattice;
        dot_ann_left:  forall x, 0 * x = 0;
        dot_distr_left:  forall x y z, (x+y)*z = x*z + y*z;
        dot_distr_leq_right: forall x y z, z*x + z*y <== z*(x+y)
    }.

    Class IdemSemiRing {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} := {
        ISR_LHISR :: LeftHandedIdemSemiRing;
        dot_ann_right: forall x, x * 0 = 0;
        dot_distr_right: forall x y z, z*(x+y) = z*x + z*y
    }.

    Class LeftHandedKleneeAlgebra {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {So : Star_Op A } := {
        LHKA_LHISR :: LeftHandedIdemSemiRing;
        star_make_right: forall x, 1 + x*x# = x#;
        star_destruct_left: forall a b, a*b <== b  ->  a#*b <== b;
    }.

    Class KleeneAlgebra {Mo : Monoid_Ops A} {SLo : SemiLattice_Ops A} {So : Star_Op A } := {
        KA_LHKA :: LeftHandedKleneeAlgebra;
        star_make_left: forall x, 1 + x#*x = x#;
        star_destruct_right: forall a b, b*a <== b  ->  b*a# <== b
    }.    

End Structures.
