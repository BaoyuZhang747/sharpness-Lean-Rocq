From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import HomologicalComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological.
Local Open Scope ring_scope.

Module DiazParkHomologicalMaps.
Section Maps.
Variable R : pzRingType.

Definition cochain_identity (C : @cochain_complex R) : cochain_map C C.
Proof.
refine (@CochainMap R C C
  (fun n => (idfun : {linear cochain_term C n -> cochain_term C n})) _).
by move=> n x.
Defined.

Definition cochain_composition (C D E : @cochain_complex R)
    (f : cochain_map C D) (g : cochain_map D E) : cochain_map C E.
Proof.
refine (@CochainMap R C E
  (fun n => (cochain_map_at g n \o cochain_map_at f n :
    {linear cochain_term C n -> cochain_term E n})) _).
by move=> n x; rewrite /= !cochain_map_commutes.
Defined.

Lemma cochain_identity_at (C : @cochain_complex R) n
    (x : cochain_term C n) : cochain_map_at (cochain_identity C) n x = x.
Proof. reflexivity. Qed.

Lemma cochain_composition_at (C D E : @cochain_complex R)
    (f : cochain_map C D) (g : cochain_map D E) n (x : cochain_term C n) :
  cochain_map_at (cochain_composition f g) n x =
    cochain_map_at g n (cochain_map_at f n x).
Proof. reflexivity. Qed.

End Maps.
End DiazParkHomologicalMaps.
