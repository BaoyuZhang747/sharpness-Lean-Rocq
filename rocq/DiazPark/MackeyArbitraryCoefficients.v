From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryModules
  ModuleInfrastructure MackeyStructures MackeySubquotients MackeyModuleCarriers
  MackeyModuleMaps MackeyFusionFiniteGeneration MackeyFiniteLength MackeyBarReduction
  FusionSystems FusionOrbit FusionMackeyShape HomologicalComplex BarPaths
  BarComplex BarNaturality BarFinitePaths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPMackeyFinite DiazParkHomological
  DiazParkBarPaths DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope ring_scope.

Module DPMackeyArbitrary.

Section FiniteCocycle.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable D : finite_category.
Variable L : functor (fc_category D) (orbit_category F).
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Variable n : nat.
Variable z : bar_term (mackey_codiagram L M) n.

Definition cocycle_seed_source (i : finite_path D n) := fobj L (finite_path_start i).
Definition cocycle_seed (i : finite_path D n) : mackey_value M (cocycle_seed_source i) :=
  @z (finite_path_start i) (finite_path_tail i).

Definition cocycle_subfunctor : mackey_subfunctor M :=
  @finitely_generated_mackey S F R M (finite_path D n)
    (@cocycle_seed_source) (@cocycle_seed).

Lemma cocycle_coordinate_mem x (p : path_from (C := fc_category D) n x) :
    subfunctor_value cocycle_subfunctor (fobj L x) (@z x p).
Proof.
have [i hi] := finite_path_decode_surjective p.
have hm := @finite_seed_contains S F R M (finite_path D n)
  (@cocycle_seed_source) (@cocycle_seed) (existT _ x i).
change (subfunctor_value cocycle_subfunctor (fobj L x)
  (@z x (finite_path_decode i))) in hm.
by rewrite hi in hm.
Qed.

Definition cocycle_lift : bar_term (mackey_codiagram L
    (subfunctor_mackey cocycle_subfunctor)) n :=
  fun x p => @submodule_in R (mackey_value M (fobj L x))
    (subfunctor_value cocycle_subfunctor (fobj L x)) (@z x p) (cocycle_coordinate_mem p).

Definition cocycle_inclusion := mackey_codiagram_map L (subfunctor_inclusion cocycle_subfunctor).

Lemma cocycle_lift_inclusion : bar_map_at cocycle_inclusion cocycle_lift = z.
Proof. reflexivity. Qed.

Lemma cocycle_inclusion_injective k : injective (bar_map_at cocycle_inclusion (n := k)).
Proof.
move=> a b he; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p; apply: submodule_val_injective.
exact (congr1 (fun v : bar_term (mackey_codiagram L M) k => v x p) he).
Qed.

Lemma cocycle_lift_closed : cocycle (bar_complex (mackey_codiagram L M)) n z ->
    cocycle (bar_complex (mackey_codiagram L
      (subfunctor_mackey cocycle_subfunctor))) n cocycle_lift.
Proof.
move=> hz; apply: (cocycle_inclusion_injective (k := n.+1)).
change (bar_map_at cocycle_inclusion
  (bar_d (mackey_codiagram L (subfunctor_mackey cocycle_subfunctor)) n cocycle_lift) =
  bar_map_at cocycle_inclusion (0 : bar_term
    (mackey_codiagram L (subfunctor_mackey cocycle_subfunctor)) n.+1)).
by rewrite -bar_map_d cocycle_lift_inclusion linear0.
Qed.

Lemma cocycle_subfunctor_finite_values P :
    module_finitely_generated (mackey_value (subfunctor_mackey cocycle_subfunctor) P).
Proof. exact: generated_values_finitely_generated. Qed.

End FiniteCocycle.

Section ArbitraryReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable K : fieldType.
Variable D : finite_category.
Variable L : functor (fc_category D) (orbit_category F).
Hypothesis simple_acyclic : forall M : mackey_module K (DPFusionMackey.fusion_mackey_shape F),
  mackey_simple M -> mackey_bar_acyclic L M.

Theorem simple_to_arbitrary_mackey_acyclic
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic L M.
Proof.
move=> n z hz.
pose N := cocycle_subfunctor (L := L) z.
have hN : mackey_finite_values (subfunctor_mackey N).
  exact: cocycle_subfunctor_finite_values.
have hc : mackey_bar_acyclic L (subfunctor_mackey N).
  apply: (@simple_to_finite_mackey_acyclic K (orbit_category F) (fc_category D)
    (DPFusionMackey.fusion_mackey_shape F) L [the finType of {group S}]
    (fun P => P) _ simple_acyclic (subfunctor_mackey N) hN).
  by move=> P; exists P.
have hl := cocycle_lift_closed hz.
have [y hy] := hc n (cocycle_lift (L := L) z) hl.
exists (bar_map_at (cocycle_inclusion (L := L) z) y).
change (bar_d (mackey_codiagram L M) n
  (bar_map_at (cocycle_inclusion (L := L) z) y) = z).
by rewrite bar_map_d hy cocycle_lift_inclusion.
Qed.

End ArbitraryReduction.
End DPMackeyArbitrary.


