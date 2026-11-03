import Sharpness.BLO.BLOEdgeCanonical
import Sharpness.BLO.BLOEdgeCollapse
import Sharpness.BLO.BLOCohomologyComparison
import Sharpness.BLO.BLOE3Native

/-! Cohomological sharpness of the actual BLO centralizer diagram.
The native restriction is the literal forgetful pullback in every degree.
The actual singular-cochain augmentation is a quasi-isomorphism; no claim
of a full homotopy equivalence, p-completion, or ring enhancement is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] [Nontrivial S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat in
theorem BLOEdgeRestrictionToLimit_isIso (n : ℕ) :
    IsIso (L.BLOEdgeRestrictionToLimit p n) := by
  letI := L.BLOCohomologyToRightKan_isIso p hS sat n
  exact L.BLOEdgeRestrictionToLimit_isIso_of_comparison p hS sat n

def BLOEdgeRestrictionIso (n : ℕ) :
    SingularCohomology.cohomology (PrimeField.{u} p) L.classifyingSpace
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≅
      limit (L.BLOCohomologyDiagram p n) := by
  letI := L.BLOEdgeRestrictionToLimit_isIso p hS sat n
  exact asIso (L.BLOEdgeRestrictionToLimit p n)

theorem BLOEdgeRestrictionIso_hom (n : ℕ) :
    (L.BLOEdgeRestrictionIso p hS sat n).hom = L.BLOEdgeRestrictionToLimit p n := rfl

@[reassoc] theorem BLOEdgeRestrictionIso_component (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOEdgeRestrictionIso p hS sat n).hom ≫ limit.π (L.BLOCohomologyDiagram p n) E =
      SingularCohomology.pull (PrimeField.{u} p)
        (categoryRealizationMap (L.BLODiagramForget E.obj))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n :=
  L.BLOEdgeRestrictionToLimit_component p n E

include hS sat in
theorem BLOEdgeReplacementEdge_isIso (n : ℕ) :
    IsIso (L.BLOEdgeReplacementEdge p n) :=
  L.BLOEdgeReplacementEdge_isIso_of_positive p
    (fun q s hs => L.BLOCohomologyPositiveIsZero p hS sat q s hs) n

include hS sat in
theorem BLOEdgeCochainAugmentation_quasiIso :
    QuasiIso (L.BLOEdgeCochainAugmentation p) :=
  L.BLOEdgeCochainAugmentation_quasiIso_of_positive_restriction p
    (fun q s hs => L.BLOCohomologyPositiveIsZero p hS sat q s hs)
    (fun n => L.BLOEdgeRestrictionToLimit_isIso p hS sat n)

def BLOEdgeAugmentationCohomologyIso (n : ℕ) :
    SingularCohomology.cohomology (PrimeField.{u} p) L.classifyingSpace
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≅
      (L.BLOEdgeTotalCochains p).homology n := by
  letI := L.BLOEdgeCochainAugmentation_quasiIso p hS sat
  exact asIso (HomologicalComplex.homologyMap (L.BLOEdgeCochainAugmentation p) n)

theorem BLOEdgeAugmentationCohomologyIso_hom (n : ℕ) :
    (L.BLOEdgeAugmentationCohomologyIso p hS sat n).hom =
      HomologicalComplex.homologyMap (L.BLOEdgeCochainAugmentation p) n := rfl

@[reassoc] theorem BLOEdgeAugmentationCohomologyIso_component (n : ℕ)
    (E : F.ElementaryCategory p) :
    (L.BLOEdgeAugmentationCohomologyIso p hS sat n).hom ≫
        HomologicalComplex.homologyMap (L.BLOEdgeTotalProjection p E) n =
      SingularCohomology.pull (PrimeField.{u} p)
        (categoryRealizationMap (L.BLODiagramForget E.obj))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n := by
  rw [BLOEdgeAugmentationCohomologyIso_hom, ← HomologicalComplex.homologyMap_comp,
    L.BLOEdgeCochainAugmentation_component]
  rfl

theorem BLOEdgeAugmentationCohomologyIso_edge (n : ℕ) :
    (L.BLOEdgeAugmentationCohomologyIso p hS sat n).hom ≫ L.BLOEdgeReplacementEdge p n =
      (L.BLOEdgeRestrictionIso p hS sat n).hom :=
  (L.BLOEdgeRestrictionToLimit_eq_edge p n).symm

include hS sat in
/-- Native positive higher limits vanish, and the canonical forgetful
restriction is invertible in every native cohomological degree, including zero. -/
theorem BLO_centralizer_decomposition_sharp :
    (∀ n s : ℕ, 0 < s → IsZero (covariantHigherLimit (PrimeField.{u} p)
      (L.BLOCohomologyDiagram p n) s)) ∧
      (∀ n : ℕ, IsIso (L.BLOEdgeRestrictionToLimit p n)) :=
  ⟨fun n s hs => L.BLOCohomologyPositiveIsZero p hS sat n s hs,
    fun n => L.BLOEdgeRestrictionToLimit_isIso p hS sat n⟩

end Sharpness.FusionSystem.CentricLinkingSystem
