(** Columnwise quasi-isomorphisms induce a quasi-isomorphism of actual
    first-quadrant chain totals, by the constructed cone comparison. *)
From mathcomp Require Import all_boot all_algebra.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism
  ChainMappingCone ChainMappingConeAcyclic ChainMappingConeReflection
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps
  FirstQuadrantChainTotalAcyclic FirstQuadrantChainCone FirstQuadrantChainConeTotalIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPChainMappingCone DPChainMappingConeAcyclic
  DPChainMappingConeReflection DPFirstQuadrantChain DPFirstQuadrantChainTotal
  DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainTotalAcyclic DPFirstQuadrantChainCone
  DPFirstQuadrantChainConeTotalIso.

Module DPFirstQuadrantChainComparison.
Section Comparison.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.
Hypothesis hcolumns : forall p, quasi_isomorphism (vertical_map f p).

Lemma column_cones_acyclic p : acyclic (vertical_complex (column_cone f) p).
Proof. rewrite column_cone_vertical; exact: mapping_cone_acyclic (hcolumns p). Qed.

Theorem total_map_quasi_isomorphism : quasi_isomorphism (total_map f).
Proof.
apply: mapping_cone_acyclic_reflects.
apply: cone_total_acyclic.
exact: total_acyclic column_cones_acyclic.
Qed.

End Comparison.
End DPFirstQuadrantChainComparison.
