import Sharpness.ReplacementConeAugmentation
import Sharpness.LinkingSubgroupRestriction

/-! The actual geometric restriction cochains augment the actual
subgroup replacement total complex. The map's projection at every
subgroup and every cochain degree is the actual singular pullback. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def subgroupCochainRestrictionCone :
    (Functor.const F.CentricOrbitᵒᵖ).obj (SingularCohomology.cochains R L.classifyingSpace A) ⟶
      L.subgroupCochainDiagram R A where
  app P := SingularCohomology.cochainPull R (L.subgroupDiagramForget P.unop) A
  naturality {P Q} a := by
    change (𝟙 _) ≫ SingularCohomology.cochainPull R (L.subgroupDiagramForget Q.unop) A =
      SingularCohomology.cochainPull R (L.subgroupDiagramForget P.unop) A ≫
        SingularCohomology.cochainPull R (L.subgroupDiagram.map a.unop) A
    rw [Category.id_comp, ← SingularCohomology.cochainPull_comp, L.subgroupDiagramForget_naturality]

def subgroupCochainAugmentation :
    SingularCohomology.cochains R L.classifyingSpace A ⟶ L.subgroupTotalCochains R A :=
  replacementConeAugmentation (L.subgroupCochainDiagram R A) (L.subgroupCochainRestrictionCone R A)

set_option backward.isDefEq.respectTransparency false in
theorem subgroupCochainAugmentation_projection (P : F.CentricOrbit) (n : ℕ) :
    (L.subgroupCochainAugmentation R A).f n ≫
      totalSummandProjectionAt (L.subgroupBicomplex R A) 0 n n (by omega) ≫
        (productCochainsProjection
          (fun t : ComposableArrows F.CentricOrbit 0 => (L.subgroupCochainDiagram R A).obj (op (chainHead t)))
          (ComposableArrows.mk₀ P)).f n =
    (SingularCohomology.cochainPull R (L.subgroupDiagramForget P) A).f n :=
  replacementConeAugmentation_projection (L.subgroupCochainDiagram R A)
    (L.subgroupCochainRestrictionCone R A) n (ComposableArrows.mk₀ P)

set_option backward.isDefEq.respectTransparency false in
theorem subgroupCochainAugmentation_component (P : F.CentricOrbit) (n : ℕ)
    (z : ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace).X n ⟶ A) :
    totalSummandProjectionAt (L.subgroupBicomplex R A) 0 n n (by omega)
        ((L.subgroupCochainAugmentation R A).f n z) (ComposableArrows.mk₀ P) =
      ((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget P)).f n ≫ z :=
  congrArg (fun t => t z) (L.subgroupCochainAugmentation_projection R A P n)

end Sharpness.FusionSystem.CentricLinkingSystem
