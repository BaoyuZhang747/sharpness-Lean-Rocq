(** Extensional laws for the actual quotient cohomology maps. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Module DPCochainMapsLaws.
Section Laws.
Variable R : pzRingType.

Lemma cohomology_ext_at (C D : cochain_complex R) (f g : cochain_map C D) n
    (h : forall x, cochain_map_at f n x = cochain_map_at g n x)
    (q : cohomology C n) : cohomology_map f n q = cohomology_map g n q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: h.
Qed.

Lemma cohomology_identity_of (C : cochain_complex R) (f : cochain_map C C) n
    (h : forall x, cochain_map_at f n x = x) (q : cohomology C n) :
  cohomology_map f n q = q.
Proof.
transitivity (cohomology_map (DiazParkHomologicalMaps.cochain_identity C) n q).
- apply cohomology_ext_at; exact h.
- exact: cohomology_map_identity.
Qed.

Lemma cohomology_composition_of (C D E : cochain_complex R)
    (f : cochain_map C D) (g : cochain_map D E) (k : cochain_map C E) n
    (h : forall x, cochain_map_at k n x = cochain_map_at g n (cochain_map_at f n x))
    (q : cohomology C n) :
  cohomology_map k n q = cohomology_map g n (cohomology_map f n q).
Proof.
rewrite -cohomology_map_composition; apply cohomology_ext_at; exact h.
Qed.
End Laws.
End DPCochainMapsLaws.
