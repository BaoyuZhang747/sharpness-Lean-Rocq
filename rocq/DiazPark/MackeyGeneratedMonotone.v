From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures MackeyGenerated.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section GeneratedMonotone.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variables X Y : forall P, mackey_value M P -> Prop.

Theorem generated_monotone
    (hXY : forall P x, @X P x -> @Y P x) P x :
    @generated_value R C B M X P x -> @generated_value R C B M Y P x.
Proof.
apply: (@generated_least R C B M X (@generated_mackey R C B M Y)).
move=> Q y hy; exact (@generated_contains R C B M Y Q y (hXY Q y hy)).
Qed.

End GeneratedMonotone.
