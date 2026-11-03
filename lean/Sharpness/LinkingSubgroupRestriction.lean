import Sharpness.LinkingSubgroupCochains
import Sharpness.SingularCohomologyEquivalence

/-! The concrete compatible family of restrictions from |L| to the actual
subgroup diagram. Its cone and native inverse-limit map are defined
without any sharpness or spectral-sequence assumptions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem subgroupDiagramForget_naturality {P Q : F.CentricOrbit} (a : P ⟶ Q) :
    L.subgroupDiagram.map a ≫ L.subgroupDiagramForget Q = L.subgroupDiagramForget P := by
  have hn : CategoryTheory.nerveMap (CostructuredArrow.map a) ≫
      CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection Q) =
      CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection P) := rfl
  exact (SSet.toTop.map_comp _ _).symm.trans (congrArg (fun f => SSet.toTop.map f) hn)

set_option backward.isDefEq.respectTransparency false in
def subgroupDiagramAugmentation : L.subgroupDiagram ⟶
    (Functor.const F.CentricOrbit).obj L.classifyingSpace where
  app := L.subgroupDiagramForget
  naturality {P Q} a := by
    change L.subgroupDiagram.map a ≫ L.subgroupDiagramForget Q =
      L.subgroupDiagramForget P ≫ 𝟙 _
    rw [Category.comp_id]
    exact L.subgroupDiagramForget_naturality a

variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def subgroupRestrictionCone (n : ℕ) : Cone (L.subgroupCohomologyDiagram R A n) where
  pt := SingularCohomology.cohomology R L.classifyingSpace A n
  π :=
    { app P := SingularCohomology.pull R (L.subgroupDiagramForget P.unop) A n
      naturality {P Q} a := by
        change (𝟙 _) ≫ SingularCohomology.pull R (L.subgroupDiagramForget Q.unop) A n =
          SingularCohomology.pull R (L.subgroupDiagramForget P.unop) A n ≫
            SingularCohomology.pull R (L.subgroupDiagram.map a.unop) A n
        rw [Category.id_comp, ← SingularCohomology.pull_comp,
          L.subgroupDiagramForget_naturality] }

def subgroupRestrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ⟶
      limit (L.subgroupCohomologyDiagram R A n) :=
  limit.lift _ (L.subgroupRestrictionCone R A n)

theorem subgroupRestrictionToLimit_component (P : F.CentricOrbit) (n : ℕ) :
    L.subgroupRestrictionToLimit R A n ≫ limit.π _ (op P) =
      SingularCohomology.pull R (L.subgroupDiagramForget P) A n :=
  limit.lift_π _ _

end Sharpness.FusionSystem.CentricLinkingSystem
