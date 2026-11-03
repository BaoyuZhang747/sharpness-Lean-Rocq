From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero
  HomologicalConnecting HomologicalDiagramLimits BarComplex BarNaturality BarDegreeZero BarExactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalDegreeZero DiazParkHomologicalConnecting
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarDegreeZero DiazParkBarExactness.
Local Open Scope ring_scope.

Module DiazParkBarConnectingLimit.
Section ConnectingLimit.
Variable R : pzRingType.
Variable C : category.
Variables A B D : module_codiagram R C.
Variables (f : nat_trans A B) (g : nat_trans B D).
Variable s : degreewise_short_exact (bar_cochain_map f) (bar_cochain_map g).

Definition limit_connecting : {linear module_limit_type D -> cohomology (bar_complex A) 1} :=
  (module_hom_to_linear (connecting_class_hom s 0) \o
    module_hom_to_linear (bar_limit_to_cycle D) :
    {linear module_limit_type D -> cohomology (bar_complex A) 1}).

Lemma limit_connecting_kernel (v : module_limit_type D) :
  limit_connecting v = 0 <->
    exists w : module_limit_type B, limit_action g w = v.
Proof.
split.
- move=> hv.
  have hq : connecting_map s 0
      (quotient_pi (boundaries_in_cycles (bar_complex D) 0) (bar_limit_to_cycle D v)) = 0.
    rewrite connecting_map_pi; exact: hv.
  have [r hr] := proj1 (connecting_map_kernel s _) hq.
  have [z hz] := quotient_pi_surjective r.
  rewrite -hz cohomology_map_pi in hr.
  have he := congr1 (cohomology_zero_cycle (bar_complex D)) hr.
  rewrite !cohomology_zero_cycle_pi in he.
  exists (bar_cycle_to_limit B z).
  apply module_limit_val_injective; apply functional_extensionality_dep => x.
  rewrite limit_action_coordinate.
  exact: (congr1 (fun t : cycle_module (bar_complex D) 0 => submodule_val t x tt) he).
- move=> [w hw].
  have he : cycle_map (bar_cochain_map g) 0 (bar_limit_to_cycle B w) = bar_limit_to_cycle D v.
    apply submodule_val_injective; apply functional_extensionality_dep => x.
    apply functional_extensionality_dep => p; case: p.
    have h := congr1 (fun t : module_limit_type D => module_limit_val t x) hw.
    rewrite limit_action_coordinate in h; exact: h.
  have hk := proj2 (connecting_map_kernel s
    (quotient_pi (boundaries_in_cycles (bar_complex D) 0) (bar_limit_to_cycle D v))).
  have hq : exists r : cohomology (bar_complex B) 0,
      cohomology_map (bar_cochain_map g) 0 r =
        quotient_pi (boundaries_in_cycles (bar_complex D) 0) (bar_limit_to_cycle D v).
    exists (quotient_pi (boundaries_in_cycles (bar_complex B) 0) (bar_limit_to_cycle B w)).
    by rewrite cohomology_map_pi he.
  move: (hk hq); rewrite connecting_map_pi; exact: id.
Qed.

Lemma limit_connecting_surjective (hB : positive_acyclic (bar_complex B)) :
  forall q : cohomology (bar_complex A) 1, exists v, limit_connecting v = q.
Proof.
move=> q.
have [r hr] := @connecting_map_surjective R (bar_complex A) (bar_complex B) (bar_complex D)
  (bar_cochain_map f) (bar_cochain_map g) s 0 (@hB 0) q.
have [z hz] := quotient_pi_surjective r.
exists (bar_cycle_to_limit D z).
change (connecting_class s (bar_limit_to_cycle D (bar_cycle_to_limit D z)) = q).
rewrite bar_limit_cycle_inverse.
by rewrite -hz connecting_map_pi in hr.
Qed.

End ConnectingLimit.
End DiazParkBarConnectingLimit.
