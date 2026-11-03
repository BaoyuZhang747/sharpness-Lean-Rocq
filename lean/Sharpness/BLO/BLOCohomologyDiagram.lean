import Sharpness.BLO.BLODiagram
import Sharpness.BLO.BLOCohomologyNative
import Sharpness.PrimeFieldScalars

/-! The cohomology functor of the actual enlarged linking-category diagram.
Its maps are native singular-cohomology pullbacks of precomposition. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]

def BLOCohomologyDiagram (n : ℕ) :
    F.ElementaryCategory p ⥤ ModuleCat.{u} (PrimeField.{u} p) :=
  (L.BLODiagram p).rightOp ⋙
    SingularCohomology.cohomologyFunctor (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n

theorem BLOCohomologyDiagram_obj (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyDiagram p n).obj E =
      SingularCohomology.cohomology (PrimeField.{u} p)
        (categoryRealization (L.BLODiagramObject E.obj))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n := rfl

theorem BLOCohomologyDiagram_map (n : ℕ) {E E' : F.ElementaryCategory p}
    (v : E ⟶ E') :
    (L.BLOCohomologyDiagram p n).map v =
      SingularCohomology.pull (PrimeField.{u} p)
        (categoryRealizationMap (L.BLODiagramPrecomp v.hom))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n := rfl

theorem BLOCohomologyDiagram_map_category (n : ℕ) {E E' : F.ElementaryCategory p}
    (v : E ⟶ E') :
    (L.BLOCohomologyDiagram p n).map v =
      BLOCohomologyPull (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramPrecomp v.hom) := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
