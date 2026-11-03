(** Equality transport on native cochain terms, cycles and cohomology, with
    literal compatibility with quotient representatives and cochain maps. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Module DPCochainDegreeTransport.
Section Transport.
Variable R : pzRingType.
Variable K : cochain_complex R.

Definition term_cast n m (h : n=m) (x : cochain_term K n) : cochain_term K m :=
  eq_rect n (cochain_term K) x m h.
Definition cycle_cast n m (h : n=m) (x : cycle_module K n) : cycle_module K m :=
  eq_rect n (cycle_module K) x m h.

Definition cohomology_degree_iso n m (h : n=m) : @isomorphism (module_category R)
    (cohomology K n) (cohomology K m).
Proof. destruct h; exact (@iso_refl (module_category R) (cohomology K n)). Defined.

Lemma cycle_cast_val n m (h : n=m) (z : cycle_module K n) :
    submodule_val (cycle_cast h z) = term_cast h (submodule_val z).
Proof. destruct h; reflexivity. Qed.

Lemma cohomology_degree_iso_pi n m (h : n=m) (z : cycle_module K n) :
    module_hom_fun (iso_hom (cohomology_degree_iso h))
      (quotient_pi (boundaries_in_cycles K n) z) =
    quotient_pi (boundaries_in_cycles K m) (cycle_cast h z).
Proof. destruct h; reflexivity. Qed.

End Transport.
Section Maps.
Variable R : pzRingType.
Variables K L : cochain_complex R.
Variable f : cochain_map K L.

Lemma cycle_cast_map n m (h : n=m) (z : cycle_module K n) :
    @cycle_cast R L n m h (cycle_map f n z) = cycle_map f m (cycle_cast h z).
Proof. destruct h; reflexivity. Qed.

End Maps.
End DPCochainDegreeTransport.
