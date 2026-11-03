import Sharpness.BLO.BLOCohomologyDiagram
import Sharpness.BLO.BLODiagramDistinguished

/-! The native subgroup restrictions from enlarged linking categories.
Precomposition and every enlarged linking arrow satisfy the explicit squares. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory

variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    (A : ModuleCat.{u} R) (n : ℕ)

def BLOCohomologyRestriction {E : F.Object} (X : L.BLODiagramObject E) :
    BLOCohomologyCategory R A n (L.BLODiagramObject E) ⟶
      OrdinaryCohomology.value R X.point.as.val A n :=
  BLOCohomologyGroupRestriction R A n X.point.as.val
    (L.BLODiagramDistinguishedFunctor X)

theorem BLOCohomologyRestriction_formula {E : F.Object} (X : L.BLODiagramObject E) :
    L.BLOCohomologyRestriction R A n X =
      SingularCohomology.pull R (L.BLODiagramSubgroupClassifyingMap X) A n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso R X.point.as.val A n).hom := rfl

theorem BLOCohomologyRestriction_precomp {E E' : F.Object} (v : E ⟶ E')
    (X : L.BLODiagramObject E') :
    BLOCohomologyPull R A n (L.BLODiagramPrecomp v) ≫
        L.BLOCohomologyRestriction R A n X =
      L.BLOCohomologyRestriction R A n ((L.BLODiagramPrecomp v).obj X) := by
  unfold BLOCohomologyRestriction
  rw [BLOCohomologyGroupRestriction_precomp, L.BLODiagramDistinguishedFunctor_precomp]
  rfl

theorem BLOCohomologyRestriction_arrow {E : F.Object} {X Y : L.BLODiagramObject E}
    (f : X ⟶ Y) :
    L.BLOCohomologyRestriction R A n X =
      L.BLOCohomologyRestriction R A n Y ≫
        OrdinaryCohomology.pull (R := R) (A := A) (L.projection.map f.val).val n := by
  unfold BLOCohomologyRestriction
  rw [BLOCohomologyGroupRestriction_eq_of_natTrans R A n
    (L.BLODiagramDistinguishedNaturality f), BLOCohomologyGroupRestriction_group]
  rfl

theorem BLOCohomologyRestriction_forget {E : F.Object} (X : L.BLODiagramObject E) :
    BLOCohomologyPull R A n (L.BLODiagramForget E) ≫
        L.BLOCohomologyRestriction R A n X =
      SingularCohomology.pull R (L.subgroupClassifyingMap X.point) A n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso R X.point.as.val A n).hom := by
  unfold BLOCohomologyPull
  rw [BLOCohomologyRestriction_formula, ← Category.assoc, ← SingularCohomology.pull_comp]
  change SingularCohomology.pull R
      (L.BLODiagramSubgroupClassifyingMap X ≫
        categoryRealizationMap (L.BLODiagramForget E)) A n ≫ _ = _
  rw [L.BLODiagramSubgroupClassifyingMap_forget]

end Sharpness.FusionSystem.CentricLinkingSystem
