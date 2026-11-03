(** The actual first differential, reindexed by vertical degree, agrees with
    signed horizontal cohomology under the proved first-page comparison. *)
From Coq Require Import Arith.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainLeading FirstQuadrantCochainEdge
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumnTerms
  FirstQuadrantCochainSpectralColumn FirstQuadrantCochainSpectralColumnClasses
  FirstQuadrantCochainSpectralSeeds FirstQuadrantCochainSpectralSeedDifferential
  CochainDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps DPFirstQuadrantLeading
  DPFirstQuadrantEdge DPColumnFiltration DPColumnRelative DPColumnFirstPage DPColumnCoordinate
  DPColumnFirstIdentification DPColumnFirstClasses DPColumnFirstSeeds DPColumnSeedDifferential
  DPCochainDegreeTransport.
Local Open Scope ring_scope.

Module DPColumnD1.
Section D1.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition row_degree p q : (q+p)%coq_nat.+1 = (q+p.+1)%coq_nat :=
  Logic.eq_sym (Nat.add_succ_r q p).

Definition first_d_row p q (x : first_page K p (q+p)%coq_nat) : first_page K p.+1 (q+p.+1)%coq_nat :=
  module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K p.+1 p.+2)
    (q+p)%coq_nat.+1 (q+p.+1)%coq_nat (row_degree p q))) (first_d x).

Lemma first_d_row_linear p q : linear (@first_d_row p q).
Proof. intros a x y; by rewrite /first_d_row linearP module_hom_linear. Qed.
HB.instance Definition _ p q := GRing.isLinear.Build R (first_page K p (q+p)%coq_nat)
  (first_page K p.+1 (q+p.+1)%coq_nat) _ (@first_d_row p q) (@first_d_row_linear p q).

Lemma column_cast_coordinate p q n (h : n=(q+p)%coq_nat) (x : column_term K p n) :
    submodule_val (@term_cast R (column_complex K p) n (q+p)%coq_nat h x)
      p q (Nat.add_comm p q) =
    submodule_val x p q (Logic.eq_trans (Nat.add_comm p q) (Logic.eq_sym h)).
Proof.
subst n; reflexivity.
Qed.

Theorem first_d_row_seed_column p q (z : cycle_module (vertical_complex K p) q) :
    module_hom_fun (iso_hom (first_page_column_iso K p.+1 q)) (first_d_row (first_seed_class z)) =
      (-1 : R)^+(p.+1*q)%N *:
        horizontal_cohomology K p q (quotient_pi (boundaries_in_cycles (vertical_complex K p) q) z).
Proof.
rewrite /first_d_row first_d_seed cohomology_degree_iso_pi first_page_column_iso_class.
rewrite /horizontal_cohomology cohomology_map_pi -linearZ.
congr (quotient_pi _ _); apply submodule_val_injective.
rewrite first_page_vertical_cycle_val cycle_cast_map.
change ((-1 : R)^+(p.+1*q)%N *:
  module_hom_fun (iso_hom (column_coordinate_iso K p.+1 q))
    (quotient_pi (relative_subspace K p.+1 p.+2 (q+p.+1)%coq_nat)
      (submodule_val (cycle_cast (row_degree p q) (seed_d_cycle z)))) =
  (-1 : R)^+(p.+1*q)%N *: horizontal K p q (submodule_val z)).
rewrite column_coordinate_iso_pi cycle_cast_val.
change ((-1 : R)^+(p.+1*q)%N *:
  submodule_val (@term_cast R (column_complex K p.+1) (q+p)%coq_nat.+1
    (q+p.+1)%coq_nat (row_degree p q) (seed_d_term z))
      p.+1 q (Nat.add_comm p.+1 q) =
  (-1 : R)^+(p.+1*q)%N *: horizontal K p q (submodule_val z)).
rewrite column_cast_coordinate.
have he : Logic.eq_trans (Nat.add_comm p.+1 q) (Logic.eq_sym (row_degree p q)) =
    horizontal_output_index (Nat.add_comm p q) by apply Prop_irrelevance.
by rewrite he seed_d_horizontal_coordinate.
Qed.

Theorem first_d_row_column p q (x : first_page K p (q+p)%coq_nat) :
    module_hom_fun (iso_hom (first_page_column_iso K p.+1 q)) (first_d_row x) =
      (-1 : R)^+q *: horizontal_cohomology K p q
        (module_hom_fun (iso_hom (first_page_column_iso K p q)) x).
Proof.
have [z <-] := first_seed_class_surjective x.
rewrite first_d_row_seed_column first_seed_column_class linearZ.
change ((-1 : R)^+(p.+1*q)%N *:
  horizontal_cohomology K p q (quotient_pi (boundaries_in_cycles (vertical_complex K p) q) z) =
  (-1 : R)^+q *: ((-1 : R)^+(p*q)%N *:
    horizontal_cohomology K p q (quotient_pi (boundaries_in_cycles (vertical_complex K p) q) z))).
by rewrite mulSn exprD scalerA.
Qed.

End D1.
End DPColumnD1.
