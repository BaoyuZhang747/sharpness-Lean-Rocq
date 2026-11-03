(** The actual cohomological edge into the kernel of the first horizontal
    map on vertical cohomology. Bijectivity is a separate obligation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps.
Local Open Scope ring_scope.

Module DPFirstQuadrantEdge.
Section Edge.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition horizontal_column_map p : cochain_map (vertical_complex K p) (vertical_complex K p.+1).
Proof.
refine (@CochainMap R (vertical_complex K p) (vertical_complex K p.+1) (horizontal K p) _).
intros n x; symmetry; exact: horizontal_vertical.
Defined.

Definition horizontal_cohomology p n := cohomology_map (horizontal_column_map p) n.

Lemma total_cocycle_horizontal_boundary n (a : total_term K n)
    (ha : cocycle (total_complex K) n a) :
    coboundary (vertical_complex K 1%N) n (horizontal K 0%N n (zero_column_at a)).
Proof.
destruct n as [|n].
- have h := f_equal (fun v : total_term K 1%N => v 1%N 0%N Logic.eq_refl) ha.
  change (horizontal K 0%N 0%N
    (a 0%N 0%N (horizontal_index (Logic.eq_refl : (1 + 0)%coq_nat = 1%N))) + 0 = 0) in h.
  have he : horizontal_index (Logic.eq_refl : (1 + 0)%coq_nat = 1%N) = Logic.eq_refl
    by apply Prop_irrelevance.
  rewrite he addr0 in h. exact h.
- have h := f_equal (fun v : total_term K n.+2 => v 1%N n.+1 Logic.eq_refl) ha.
  change (horizontal K 0%N n.+1
    (a 0%N n.+1 (horizontal_index (Logic.eq_refl : (1 + n.+1)%coq_nat = n.+2))) +
    (-1 : R)^+1 *: vertical K 1%N n
      (a 1%N n (vertical_index (Logic.eq_refl : (1 + n.+1)%coq_nat = n.+2))) = 0) in h.
  have eh : horizontal_index (Logic.eq_refl : (1 + n.+1)%coq_nat = n.+2) = Logic.eq_refl
    by apply Prop_irrelevance.
  have ev : vertical_index (Logic.eq_refl : (1 + n.+1)%coq_nat = n.+2) = Logic.eq_refl
    by apply Prop_irrelevance.
  rewrite eh ev expr1 scaleN1r in h.
  exists (a 1%N n Logic.eq_refl).
  symmetry; exact (subr0_eq h).
Qed.

Lemma zero_column_cohomology_kernel n (x : cohomology (total_complex K) n) :
    horizontal_cohomology 0%N n (cohomology_map (zero_column_projection K) n x) = 0.
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite /horizontal_cohomology !cohomology_map_pi.
apply/quotient_pi_kernel; apply/boundary_subspaceE.
exact (@total_cocycle_horizontal_boundary n
  (cycle_inclusion (total_complex K) n z) (submodule_val_mem z)).
Qed.

Definition edge_kernel n := linear_kernel (horizontal_cohomology 0%N n).
Definition edge_module n := submodule_carrier (edge_kernel n).

Definition edge_map_fun n (x : cohomology (total_complex K) n) : edge_module n :=
  @submodule_in R (cohomology (vertical_complex K 0%N) n) (edge_kernel n)
    (cohomology_map (zero_column_projection K) n x) (zero_column_cohomology_kernel x).

Lemma edge_map_linear n : linear (@edge_map_fun n).
Proof.
intros r x y; apply submodule_val_injective.
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (cohomology (total_complex K) n)
  (edge_module n) _ (@edge_map_fun n) (@edge_map_linear n).

Definition edge_map n : {linear cohomology (total_complex K) n -> edge_module n} :=
  (@edge_map_fun n : {linear _ -> _}).

Theorem edge_map_component n (x : cohomology (total_complex K) n) :
    submodule_val (edge_map n x) = cohomology_map (zero_column_projection K) n x.
Proof. reflexivity. Qed.

Definition positive_horizontal_exact : Prop :=
  forall n p (x : cohomology (vertical_complex K p.+1) n),
    horizontal_cohomology p.+1 n x = 0 ->
    exists y : cohomology (vertical_complex K p) n, horizontal_cohomology p n y = x.
End Edge.
End DPFirstQuadrantEdge.
