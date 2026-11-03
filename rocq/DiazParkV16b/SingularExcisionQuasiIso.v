(** The proved open-cover excision isomorphism certifies its literal relative chain map. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness HomologicalModuleIso.
From DiazParkV16b Require Import ChainHomologyMaps ChainQuasiIsomorphism SingularExcisionRelative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomologicalModuleIso DPChainHomologyMaps DPChainQuasiIsomorphism DPSingularExcisionRelative.
Local Open Scope classical_set_scope.
Module DPSingularExcisionQuasiIso.
Theorem relative_excision_quasi_isomorphism (Real : realType) (R : pzRingType)
    (X : topologicalType) (A B : set X) (hA : open A) (hB : open B)
    (hc : forall x, A x \/ B x) :
    quasi_isomorphism (relative_excision_map Real R A B).
Proof.
move=> n; pose e := relative_excision_homology_iso Real R hA hB hc n; split.
- move=> x y hxy; apply: (module_iso_hom_injective (e := e)).
  by rewrite /e !relative_excision_homology_iso_hom.
- move=> y; exists (module_hom_fun (iso_inv e) y).
  rewrite -(@relative_excision_homology_iso_hom Real R X A B hA hB hc n).
  exact (@module_iso_inv_hom_apply R _ _ e y).
Qed.
End DPSingularExcisionQuasiIso.
