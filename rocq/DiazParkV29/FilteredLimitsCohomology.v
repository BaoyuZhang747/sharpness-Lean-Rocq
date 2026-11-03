(** Cohomology commutes with a directed colimit of nonnegative complexes.
    The two termwise hypotheses are the concrete representative and eventual
    zero properties of a colimit; the finite-category application proves them. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryLimits CategoryColimitMaps ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps.
From DiazParkV29 Require Import FilteredLimitsDirected.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DiazParkHomological DiazParkHomologicalMaps
  DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Module DPFilteredCohomology.

Lemma cohomology_map_ext (R : pzRingType) (C D : @cochain_complex R)
    (f g : cochain_map C D) n
    (h : forall x, cochain_map_at f n x = cochain_map_at g n x) q :
    cohomology_map f n q = cohomology_map g n q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: h.
Qed.

Record directed_complex (R : pzRingType) (I : directed_poset) := DirectedComplex {
  dc_value : stage I -> @cochain_complex R;
  dc_map : forall i j, stage_le i j -> cochain_map (dc_value i) (dc_value j);
  dc_id : forall i (h : stage_le i i) n x, cochain_map_at (dc_map h) n x = x;
  dc_comp : forall i j k (h : stage_le i j) (g : stage_le j k) n x,
    cochain_map_at (dc_map g) n (cochain_map_at (dc_map h) n x) =
      cochain_map_at (dc_map (stage_trans h g)) n x
}.
Arguments dc_value {_ _} _ _.
Arguments dc_map {_ _} _ {_ _} _.
Arguments dc_id {_ _} _ {_} _ _ _.
Arguments dc_comp {_ _} _ {_ _ _} _ _ _ _.

Section Comparison.
Variable R : pzRingType.
Variable I : directed_poset.
Variable X : directed_complex R I.
Variable C : @cochain_complex R.
Variable leg : forall i, cochain_map (dc_value X i) C.
Hypothesis leg_natural : forall i j (h : stage_le i j) n x,
  cochain_map_at (leg j) n (cochain_map_at (dc_map X h) n x) =
    cochain_map_at (leg i) n x.

Definition termwise_representatives := forall n (x : cochain_term C n),
  exists i (v : cochain_term (dc_value X i) n), cochain_map_at (leg i) n v = x.
Definition termwise_eventual_zero := forall i n (x : cochain_term (dc_value X i) n),
  cochain_map_at (leg i) n x = 0 ->
  exists j (h : stage_le i j), cochain_map_at (dc_map X h) n x = 0.

Hypothesis representatives : termwise_representatives.
Hypothesis eventual_zero : termwise_eventual_zero.

Definition cohomology_system (n : nat) : directed_module R I.
Proof.
refine (@DirectedModule R I (fun i => [the lmodType R of cohomology (dc_value X i) n])
  (fun i j h => cohomology_map (dc_map X h) n) _ _).
- move=> i h q.
  transitivity (cohomology_map (cochain_identity (dc_value X i)) n q).
  + apply cohomology_map_ext => x; exact: dc_id.
  + exact: cohomology_map_identity.
- move=> i j k h g q.
  rewrite -cohomology_map_composition.
  apply cohomology_map_ext => x; exact: dc_comp.
Defined.

Lemma cohomology_leg_natural i j (h : stage_le i j) n q :
    cohomology_map (leg j) n (dm_map (cohomology_system n) h q) =
      cohomology_map (leg i) n q.
Proof.
change (cohomology_map (leg j) n (cohomology_map (dc_map X h) n q) = cohomology_map (leg i) n q).
rewrite -cohomology_map_composition.
apply cohomology_map_ext => x; exact: leg_natural.
Qed.

Definition cohomology_cocone n :
    cocone (module_system_functor (cohomology_system n))
      [the lmodType R of cohomology C n].
Proof.
refine (@Build_cocone (stage_category I) (module_category R)
  (module_system_functor (cohomology_system n)) [the lmodType R of cohomology C n]
  (fun i => module_hom_of_linear (cohomology_map (leg i) n)) _).
move=> i j h; apply module_hom_ext=> q; exact: cohomology_leg_natural.
Defined.

Definition cohomology_comparison n :
    module_hom (colimit_module (cohomology_system n)) [the lmodType R of cohomology C n] :=
  module_colimit_desc (cohomology_cocone n).

Lemma cohomology_comparison_in n i (q : cohomology (dc_value X i) n) :
    cohomology_comparison n (colimit_in (V := cohomology_system n) q) =
      cohomology_map (leg i) n q.
Proof. exact: module_colimit_desc_in. Qed.

Lemma cycle_representative n (z : cochain_term C n) (hz : cocycle C n z) :
    exists i (v : cochain_term (dc_value X i) n),
      cocycle (dc_value X i) n v /\ cochain_map_at (leg i) n v = z.
Proof.
have [i [v hv]] := representatives z.
have hd : cochain_map_at (leg i) n.+1 (cochain_d (dc_value X i) n v) = 0.
  rewrite -cochain_map_commutes hv; exact hz.
have [j [h he]] := eventual_zero hd.
exists j, (cochain_map_at (dc_map X h) n v); split.
- rewrite /cocycle cochain_map_commutes; exact he.
- rewrite leg_natural; exact hv.
Qed.

Theorem cohomology_comparison_surjective n :
    forall q : cohomology C n, exists x, cohomology_comparison n x = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
have hz : cocycle C n (cycle_inclusion C n z) := submodule_val_mem z.
have [i [v [hv he]]] := cycle_representative hz.
exists (colimit_in (V := cohomology_system n) (cohomology_class hv)).
rewrite cohomology_comparison_in cohomology_map_class /cohomology_class.
congr (quotient_pi _ _); apply submodule_val_injective; exact he.
Qed.

Lemma boundary_eventual i n (z : cochain_term (dc_value X i) n)
    (hz : coboundary C n (cochain_map_at (leg i) n z)) :
    exists j (h : stage_le i j),
      coboundary (dc_value X j) n (cochain_map_at (dc_map X h) n z).
Proof.
case: n z hz => [|n] z hz.
- exact: eventual_zero hz.
- have [y hy] := hz.
  have [j [v hv]] := representatives y.
  pose k := upper i j.
  have hi : stage_le i k := le_upper_l i j.
  have hj : stage_le j k := le_upper_r i j.
  pose w := cochain_map_at (dc_map X hi) n.+1 z -
    cochain_d (dc_value X k) n (cochain_map_at (dc_map X hj) n v).
  have hw : cochain_map_at (leg k) n.+1 w = 0.
    rewrite /w linearB leg_natural -cochain_map_commutes leg_natural hv hy subrr.
    reflexivity.
  have [l [hkl he]] := eventual_zero hw.
  exists l, (stage_trans hi hkl).
  exists (cochain_map_at (dc_map X (stage_trans hj hkl)) n v).
  have he' : cochain_map_at (dc_map X hkl) n.+1 (cochain_map_at (dc_map X hi) n.+1 z) =
      cochain_d (dc_value X l) n
        (cochain_map_at (dc_map X hkl) n (cochain_map_at (dc_map X hj) n v)).
    apply/eqP; rewrite -subr_eq0 cochain_map_commutes -linearB; apply/eqP; exact he.
  rewrite !dc_comp in he'; exact: esym he'.
Qed.

Theorem cohomology_comparison_kernel n x : cohomology_comparison n x = 0 -> x = 0.
Proof.
have [i [q <-]] := colimit_in_surjective x.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_comparison_in cohomology_map_pi.
move/quotient_pi_kernel=> hb.
have hz : coboundary C n (cochain_map_at (leg i) n (cycle_inclusion (dc_value X i) n z)).
  apply/boundary_subspaceE; exact hb.
have [j [h he]] := boundary_eventual hz.
apply/colimit_in_zero; exists j, h.
change (cohomology_map (dc_map X h) n (quotient_pi (boundaries_in_cycles (dc_value X i) n) z) = 0).
rewrite cohomology_map_pi; apply/quotient_pi_kernel; apply/boundary_subspaceE.
exact he.
Qed.

Theorem cohomology_comparison_injective n : injective (cohomology_comparison n).
Proof.
move=> x y he; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply cohomology_comparison_kernel; rewrite module_hom_sub he subrr; reflexivity.
Qed.

Definition comparison_inverse n (q : cohomology C n) : colimit_module (cohomology_system n) :=
  proj1_sig (constructive_indefinite_description (cohomology_comparison_surjective q)).
Arguments comparison_inverse n q : clear implicits.
Lemma comparison_inverse_right n q : cohomology_comparison n (comparison_inverse n q) = q.
Proof. exact: (proj2_sig (constructive_indefinite_description (cohomology_comparison_surjective q))). Qed.
Lemma comparison_inverse_left n x : comparison_inverse n (cohomology_comparison n x) = x.
Proof. apply cohomology_comparison_injective; exact: comparison_inverse_right. Qed.
Lemma comparison_inverse_linear n : linear (comparison_inverse n).
Proof.
move=> a x y; apply cohomology_comparison_injective.
rewrite comparison_inverse_right module_hom_linear !comparison_inverse_right; reflexivity.
Qed.

Definition cohomology_colimit_iso n : @isomorphism (module_category R)
    (colimit_module (cohomology_system n)) [the lmodType R of cohomology C n].
Proof.
refine (@Build_isomorphism (module_category R) _ _ (cohomology_comparison n)
  (exist _ (comparison_inverse n) (@comparison_inverse_linear n)) _ _).
- apply module_hom_ext=> x; exact: comparison_inverse_left.
- apply module_hom_ext=> x; exact: comparison_inverse_right.
Defined.

End Comparison.
End DPFilteredCohomology.
