(** Left translation on invariant homogeneous cochains induces precisely the
    native conjugation pullback. The normalization discrepancy is removed by
    the proved identity action of right translation on cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom
  CategoryComplexIso HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  BarFreeModule MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousPaths GroupCohomologyHomogeneousMaps
  GroupCohomologyHomogeneousComplex GroupCohomologyHomogeneousEquivariance
  GroupCohomologyHomogeneousCohomology GroupCohomologyHomogeneousSemilinear
  GroupCohomologyHomogeneousRightTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyPullback DiazParkFreeModule
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPGroupCohomologyHomogeneousPaths DPGroupCohomologyHomogeneousMaps
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousCohomology DPGroupCohomologyHomogeneousSemilinear
  DPGroupCohomologyHomogeneousRightTranslation.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousConjugation.
Section Conjugation.
Variable G : finGroupType.
Variables L P : {group G}.
Variable x : G.
Hypothesis h : L \subset (P :^ x)%g.
Local Notation LS := [the finGroupType of [subg L]].
Local Notation PS := [the finGroupType of [subg P]].

Lemma conjugate_mem (a : LS) : (val a ^ x^-1)%g \in P.
Proof. have hh := subsetP h _ (subgP a); by rewrite mem_conjg in hh. Qed.

Definition subgroup_conjugation_hom : {morphism [set: LS] >-> PS}.
Proof.
apply: (Morphism (mfun := fun a : LS => subg P (val a ^ x^-1)%g)).
move=> a b _ _; rewrite conjMg.
apply: subgM; exact: conjugate_mem.
Defined.

Lemma subgroup_conjugation_hom_val (a : LS) :
  val (subgroup_conjugation_hom a) = (val a ^ x^-1)%g.
Proof. apply: subgK; exact: conjugate_mem. Qed.

Lemma left_conjugation_equivariant (a : LS) t :
  (x * (val a * t))%g = (val (subgroup_conjugation_hom a) * (x*t))%g.
Proof.
rewrite subgroup_conjugation_hom_val /conjg invgK !mulgA mulgKV; reflexivity.
Qed.

Lemma normalized_conjugation_equivariant (a : LS) t :
  ((val a * t) ^ x^-1)%g =
    (val (subgroup_conjugation_hom a) * (t ^ x^-1))%g.
Proof. by rewrite subgroup_conjugation_hom_val conjMg. Qed.

Variable R : comPzRingType.
Variable A : lmodType R.

Definition ambient_left_conjugation :=
  @ambient_semilinear R G G L P subgroup_conjugation_hom
    (fun t => (x*t)%g) left_conjugation_equivariant A.

Definition ambient_normalized_conjugation :=
  @ambient_semilinear R G G L P subgroup_conjugation_hom
    (fun t => (t ^ x^-1)%g) normalized_conjugation_equivariant A.

Lemma left_vertices n (v : power G n) :
  vertices_map (fun t => (x*t)%g) n v = left_translate n x v.
Proof.
elim: n v => [|n IH] v; first by case: v.
by case: v => a v; rewrite /= IH.
Qed.

Lemma ambient_left_conjugation_component n
    (f : cochain_term (@ambient_hom_complex R G P A) n) a v :
  module_hom_fun (component (cochain_map_at ambient_left_conjugation n f) a) v =
    module_hom_fun (component f tt) (homogeneous_action R n x v).
Proof.
change (module_hom_fun (component f tt) (homogeneous_map R (fun t => (x*t)%g) n v) =
  module_hom_fun (component f tt) (homogeneous_action R n x v)).
rewrite /homogeneous_map /homogeneous_action; congr (module_hom_fun _ (free_map R _ v)).
apply functional_extensionality_dep => w; exact: left_vertices.
Qed.

Lemma conjugation_normalization_cochain n
    (f : cochain_term (@ambient_hom_complex R G P A) n) :
  cochain_map_at ambient_left_conjugation n
    (cochain_map_at (@ambient_right_translation R G P x^-1 A) n f) =
    cochain_map_at ambient_normalized_conjugation n f.
Proof.
apply diagram_hom_ext => a v; case: a v => v.
change (module_hom_fun (component f tt)
    (homogeneous_map R (fun t => (t*x^-1)%g) n
      (homogeneous_map R (fun t => (x*t)%g) n v)) =
  module_hom_fun (component f tt)
    (homogeneous_map R (fun t => (t ^ x^-1)%g) n v)).
rewrite /homogeneous_map -free_map_composition.
congr (module_hom_fun _ (free_map R _ v)).
apply functional_extensionality_dep => w.
change (vertices_map (fun t => (t*x^-1)%g) n.+1
    (vertices_map (fun t => (x*t)%g) n.+1 w) =
  vertices_map (fun t => (t ^ x^-1)%g) n.+1 w).
rewrite -vertices_map_composition.
congr (vertices_map _ n.+1 w); apply functional_extensionality_dep => t.
by rewrite /conjg invgK mulgA.
Qed.

Lemma conjugation_normalization_cohomology n
    (q : cohomology (@ambient_hom_complex R G P A) n) :
  cohomology_map ambient_left_conjugation n q =
    cohomology_map ambient_normalized_conjugation n q.
Proof.
rewrite -{1}(@ambient_right_translation_cohomology_identity R G P x^-1 A n q).
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: conjugation_normalization_cochain.
Qed.

Theorem ambient_left_conjugation_native_square n :
  module_hom_comp (module_hom_of_linear (cohomology_map ambient_left_conjugation n))
    (iso_hom (@ambient_native_iso R G L A n)) =
  module_hom_comp (iso_hom (@ambient_native_iso R G P A n))
    (pull A subgroup_conjugation_hom n).
Proof.
transitivity (module_hom_comp
  (module_hom_of_linear (cohomology_map ambient_normalized_conjugation n))
  (iso_hom (@ambient_native_iso R G L A n))).
- apply module_hom_ext => q.
  change (module_hom_fun (iso_hom (@ambient_native_iso R G L A n))
      (cohomology_map ambient_left_conjugation n q) =
    module_hom_fun (iso_hom (@ambient_native_iso R G L A n))
      (cohomology_map ambient_normalized_conjugation n q)).
  by rewrite conjugation_normalization_cohomology.
- apply: ambient_semilinear_native_cohomology_square.
  move=> a; symmetry; exact: subgroup_conjugation_hom_val.
Qed.

End Conjugation.
End DPGroupCohomologyHomogeneousConjugation.

