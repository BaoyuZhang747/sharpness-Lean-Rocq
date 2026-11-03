import Sharpness.V28.Cohomology
import Sharpness.Unconditional.SubgroupDecompositionSharpness

/-! Sharpness and the literal restriction maps of the subgroup decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem.V28
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k)

include p hS sat

theorem subgroupCohomology_acyclic (n : ℕ) :
    Acyclic (L.subgroupCohomologyDiagram k A n) :=
  acyclic_of_iso (L.subgroupCohomologyCoefficientIso p k A n hS sat)
    (FusionSystem.V28.cohomology_acyclic p k F hS sat (A := A) n)

theorem subgroupRestrictionToLimit_isIso (n : ℕ) :
    IsIso (L.subgroupRestrictionToLimit k A n) :=
  L.subgroupRestrictionToLimit_isIso_of_acyclic k A
    (fun q => subgroupCohomology_acyclic L p hS sat k A q) n

theorem subgroup_decomposition_sharp :
    (∀ i n : ℕ, 0 < i → IsZero (higherLimit (L.subgroupCohomologyDiagram k A n) i)) ∧
      (∀ n : ℕ, IsIso (L.subgroupRestrictionToLimit k A n)) :=
  ⟨fun i n hi => subgroupCohomology_acyclic L p hS sat k A n i hi,
    fun n => subgroupRestrictionToLimit_isIso L p hS sat k A n⟩

theorem nativeOrdinaryRestrictionToLimit_isIso (n : ℕ) :
    IsIso (L.nativeOrdinaryRestrictionToLimit p hS sat k A n) := by
  letI := subgroupRestrictionToLimit_isIso L p hS sat k A n
  exact L.nativeOrdinaryRestrictionToLimit_isIso_of_subgroup p hS sat k A n

def nativeOrdinaryRestrictionIso (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (F.cohomologyCoefficient (R := k) (A := A) n) := by
  letI := nativeOrdinaryRestrictionToLimit_isIso L p hS sat k A n
  exact asIso (L.nativeOrdinaryRestrictionToLimit p hS sat k A n)

theorem nativeOrdinaryRestrictionIso_hom (n : ℕ) :
    (nativeOrdinaryRestrictionIso L p hS sat k A n).hom =
      L.nativeOrdinaryRestrictionToLimit p hS sat k A n := rfl

theorem nativeOrdinaryRestrictionIso_component (n : ℕ) (P : F.CentricOrbit) :
    (nativeOrdinaryRestrictionIso L p hS sat k A n).hom ≫
        limit.π (F.cohomologyCoefficient (R := k) (A := A) n) (op P) =
      SingularCohomology.pull k (L.subgroupClassifyingMap (L.linkingObjectOfOrbit P)) A n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso k P.obj.as.subgroup A n).hom :=
  L.nativeOrdinaryRestrictionToLimit_component p hS sat k A n P

def subgroupRestrictionIso (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.subgroupCohomologyDiagram k A n) := by
  letI := subgroupRestrictionToLimit_isIso L p hS sat k A n
  exact asIso (L.subgroupRestrictionToLimit k A n)

theorem subgroupRestrictionIso_hom (n : ℕ) :
    (subgroupRestrictionIso L p hS sat k A n).hom =
      L.subgroupRestrictionToLimit k A n := rfl

theorem subgroupRestrictionIso_component (n : ℕ) (P : F.CentricOrbit) :
    (subgroupRestrictionIso L p hS sat k A n).hom ≫
        limit.π (L.subgroupCohomologyDiagram k A n) (op P) =
      SingularCohomology.pull k (L.subgroupDiagramForget P) A n :=
  L.subgroupRestrictionToLimit_component k A P n

end Sharpness.FusionSystem.CentricLinkingSystem.V28
