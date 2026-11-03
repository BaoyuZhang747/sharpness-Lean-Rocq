import Sharpness.BLO.BLOCohomologyDiagram
import Sharpness.BLO.BLOEdgeCochain
import Sharpness.BLO.BLOEdgeRan

/-! Actual forgetful restrictions and the replacement edge for BLO's
enlarged linking categories. The double-opposite indexing equivalence is
made explicit, so the final limit has the direct elementary-category variance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]

def BLOEdgeCochainDiagram :
    (F.ElementaryCategory p)ᵒᵖᵒᵖ ⥤ CochainComplex (ModuleCat.{u} (PrimeField.{u} p)) ℕ :=
  BLOEdge.cochainDiagram (L.BLODiagram p) (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p))

def BLOEdgeTotalCochains : CochainComplex (ModuleCat.{u} (PrimeField.{u} p)) ℕ :=
  cochainReplacementTotal (L.BLOEdgeCochainDiagram p)

def BLOEdgeReplacementCohomologyDiagram (n : ℕ) :
    (F.ElementaryCategory p)ᵒᵖᵒᵖ ⥤ ModuleCat.{u} (PrimeField.{u} p) :=
  replacementCohomologyDiagram (L.BLOEdgeCochainDiagram p) n

theorem BLOEdgeReplacementCohomologyDiagram_eq (n : ℕ) :
    L.BLOEdgeReplacementCohomologyDiagram p n =
      unopUnop (F.ElementaryCategory p) ⋙ L.BLOCohomologyDiagram p n := rfl

def BLOEdgeReplacementLimitIso (n : ℕ) :
    limit (L.BLOEdgeReplacementCohomologyDiagram p n) ≅
      limit (L.BLOCohomologyDiagram p n) :=
  Functor.Initial.limitIso (unopUnop (F.ElementaryCategory p))
    (L.BLOCohomologyDiagram p n)

@[reassoc] theorem BLOEdgeReplacementLimitIso_component (n : ℕ)
    (E : F.ElementaryCategory p) :
    (L.BLOEdgeReplacementLimitIso p n).hom ≫
        limit.π (L.BLOCohomologyDiagram p n) E =
      limit.π (L.BLOEdgeReplacementCohomologyDiagram p n) (op (op E)) := by
  apply (cancel_epi (L.BLOEdgeReplacementLimitIso p n).inv).1
  rw [Iso.inv_hom_id_assoc]
  exact (limit.pre_π (L.BLOCohomologyDiagram p n)
    (unopUnop (F.ElementaryCategory p)) (op (op E))).symm

def BLOEdgeReplacementHigherLimitIso (n s : ℕ) :
    higherLimit (L.BLOEdgeReplacementCohomologyDiagram p n) s ≅
      covariantHigherLimit (PrimeField.{u} p) (L.BLOCohomologyDiagram p n) s := by
  rw [BLOEdgeReplacementCohomologyDiagram_eq]
  exact (covariantHigherLimitEquivalenceIso (PrimeField.{u} p)
    (opOpEquivalence (F.ElementaryCategory p)) (L.BLOCohomologyDiagram p n) s).symm

def BLOEdgeRestrictionCone (n : ℕ) : Cone (L.BLOCohomologyDiagram p n) where
  pt := SingularCohomology.cohomology (PrimeField.{u} p) L.classifyingSpace
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
  π :=
    { app E := SingularCohomology.pull (PrimeField.{u} p)
        ((L.BLODiagramForgetfulCocone p).ι.app (op E))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
      naturality {E E'} f := by
        change (𝟙 _) ≫ SingularCohomology.pull (PrimeField.{u} p)
          ((L.BLODiagramForgetfulCocone p).ι.app (op E')) _ n =
          SingularCohomology.pull (PrimeField.{u} p)
            ((L.BLODiagramForgetfulCocone p).ι.app (op E)) _ n ≫
          SingularCohomology.pull (PrimeField.{u} p) ((L.BLODiagram p).map f.op) _ n
        rw [Category.id_comp, ← SingularCohomology.pull_comp,
          (L.BLODiagramForgetfulCocone p).w f.op] }

def BLOEdgeRestrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology (PrimeField.{u} p) L.classifyingSpace
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ⟶
      limit (L.BLOCohomologyDiagram p n) :=
  limit.lift _ (L.BLOEdgeRestrictionCone p n)

@[reassoc] theorem BLOEdgeRestrictionToLimit_component (n : ℕ)
    (E : F.ElementaryCategory p) :
    L.BLOEdgeRestrictionToLimit p n ≫ limit.π (L.BLOCohomologyDiagram p n) E =
      SingularCohomology.pull (PrimeField.{u} p)
        (categoryRealizationMap (L.BLODiagramForget E.obj))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n :=
  limit.lift_π _ _

def BLOEdgeCochainAugmentation :
    SingularCohomology.cochains (PrimeField.{u} p) L.classifyingSpace
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) ⟶
      L.BLOEdgeTotalCochains p :=
  BLOEdge.cochainAugmentation (L.BLODiagram p) (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) (L.BLODiagramForgetfulCocone p)

def BLOEdgeTotalProjection (E : F.ElementaryCategory p) :
    L.BLOEdgeTotalCochains p ⟶ SingularCohomology.cochains (PrimeField.{u} p)
      ((L.BLODiagram p).obj (op E)) (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) :=
  BLOEdge.totalProjection (L.BLODiagram p) (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) (op E)

@[reassoc] theorem BLOEdgeCochainAugmentation_component (E : F.ElementaryCategory p) :
    L.BLOEdgeCochainAugmentation p ≫ L.BLOEdgeTotalProjection p E =
      SingularCohomology.cochainPull (PrimeField.{u} p)
        (categoryRealizationMap (L.BLODiagramForget E.obj))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) :=
  BLOEdge.cochainAugmentation_projection (L.BLODiagram p) (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) (L.BLODiagramForgetfulCocone p) (op E)

def BLOEdgeReplacementEdge (n : ℕ) :
    (L.BLOEdgeTotalCochains p).homology n ⟶ limit (L.BLOCohomologyDiagram p n) :=
  elementaryReplacementLimitEdge (L.BLOEdgeCochainDiagram p) n ≫
    (L.BLOEdgeReplacementLimitIso p n).hom

@[reassoc] theorem BLOEdgeReplacementEdge_component (n : ℕ)
    (E : F.ElementaryCategory p) :
    L.BLOEdgeReplacementEdge p n ≫ limit.π (L.BLOCohomologyDiagram p n) E =
      HomologicalComplex.homologyMap (L.BLOEdgeTotalProjection p E) n := by
  rw [BLOEdgeReplacementEdge, Category.assoc, BLOEdgeReplacementLimitIso_component]
  exact elementaryReplacementLimitEdge_component (L.BLOEdgeCochainDiagram p) n (op E)

theorem BLOEdgeRestrictionToLimit_eq_edge (n : ℕ) :
    L.BLOEdgeRestrictionToLimit p n =
      HomologicalComplex.homologyMap (L.BLOEdgeCochainAugmentation p) n ≫
        L.BLOEdgeReplacementEdge p n := by
  apply limit.hom_ext
  intro E
  rw [Category.assoc, BLOEdgeReplacementEdge_component,
    ← HomologicalComplex.homologyMap_comp, BLOEdgeCochainAugmentation_component]
  exact BLOEdgeRestrictionToLimit_component L p n E

end Sharpness.FusionSystem.CentricLinkingSystem
