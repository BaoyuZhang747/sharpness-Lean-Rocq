import Sharpness.Unconditional.SubgroupOrdinaryRestriction
import Sharpness.Unconditional.SubgroupDecompositionAugmentation
import Sharpness.Unconditional.ElementaryReplacementLimitEdge

/-! Sharpness of the actual subgroup decomposition, with the literal
geometric restriction map. The proof uses the elementary replacement edge
and the constructed augmentation, without spectral sequences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem subgroupRestrictionToLimit_eq_elementary (n : ℕ) :
    L.subgroupRestrictionToLimit R A n =
      HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n ≫
        elementaryReplacementLimitEdge (L.subgroupCochainDiagram R A) n := by
  apply limit.hom_ext
  intro P
  rw [Category.assoc]
  rw [show elementaryReplacementLimitEdge (L.subgroupCochainDiagram R A) n ≫
      limit.π (L.subgroupCohomologyDiagram R A n) P = _ from
    elementaryReplacementLimitEdge_component (L.subgroupCochainDiagram R A) n P.unop]
  exact (L.subgroupRestrictionToLimit_component R A P.unop n).trans
    (L.subgroupAugmentationCohomology_component R A P.unop n).symm

theorem subgroupRestrictionToLimit_isIso_of_acyclic
    (h : ∀ n, Acyclic (L.subgroupCohomologyDiagram R A n)) (n : ℕ) :
    IsIso (L.subgroupRestrictionToLimit R A n) := by
  letI := L.subgroupCochainAugmentation_quasiIso_unconditional R A
  letI := elementaryReplacementLimitEdge_isIso (L.subgroupCochainDiagram R A)
    (fun q j => h q (j+1) (Nat.succ_pos _)) n
  rw [L.subgroupRestrictionToLimit_eq_elementary R A n]
  infer_instance

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
include hS sat

theorem subgroupRestrictionToLimit_isIso_unconditional
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ) :
    IsIso (L.subgroupRestrictionToLimit k A n) :=
  L.subgroupRestrictionToLimit_isIso_of_acyclic k A
    (fun q => L.subgroupCohomology_acyclic_unconditional p hS sat k A q) n

/-- Both defining conclusions of sharpness for the actual subgroup diagram. -/
theorem centric_subgroup_decomposition_sharp_unconditional
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) :
    (∀ i n : ℕ, 0 < i → IsZero (higherLimit (L.subgroupCohomologyDiagram k A n) i)) ∧
      (∀ n : ℕ, IsIso (L.subgroupRestrictionToLimit k A n)) :=
  ⟨fun i n hi => L.subgroupCohomology_acyclic_unconditional p hS sat k A n i hi,
    fun n => L.subgroupRestrictionToLimit_isIso_unconditional p hS sat k A n⟩

theorem centric_subgroup_decomposition_primeLocal_sharp_unconditional
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) :
    (∀ i n : ℕ, 0 < i → IsZero (higherLimit
      (L.subgroupCohomologyDiagram (PrimeLocalRing.{u} p) A n) i)) ∧
      (∀ n : ℕ, IsIso (L.subgroupRestrictionToLimit (PrimeLocalRing.{u} p) A n)) :=
  ⟨fun i n hi => L.subgroupCohomology_primeLocal_acyclic_unconditional p hS sat A n i hi,
    fun n => L.subgroupRestrictionToLimit_isIso_of_acyclic (PrimeLocalRing.{u} p) A
      (fun q => L.subgroupCohomology_primeLocal_acyclic_unconditional p hS sat A q) n⟩

theorem nativeOrdinaryRestrictionToLimit_isIso_unconditional
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ) :
    IsIso (L.nativeOrdinaryRestrictionToLimit p hS sat k A n) := by
  letI := L.subgroupRestrictionToLimit_isIso_unconditional p hS sat k A n
  exact L.nativeOrdinaryRestrictionToLimit_isIso_of_subgroup p hS sat k A n

def subgroupRestrictionIso_unconditional
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.subgroupCohomologyDiagram k A n) := by
  letI := L.subgroupRestrictionToLimit_isIso_unconditional p hS sat k A n
  exact asIso (L.subgroupRestrictionToLimit k A n)

theorem subgroupRestrictionIso_unconditional_hom
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ) :
    (L.subgroupRestrictionIso_unconditional p hS sat k A n).hom =
      L.subgroupRestrictionToLimit k A n := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
