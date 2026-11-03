import Sharpness.LinkingSubgroupDiagram
import Sharpness.SingularCohomologyEquivalence
import Sharpness.Saturation

/-! Precisely the BP comparison of BLO Proposition 2.2 (pp.12--13),
restated as AKO III.5.29(b), p.200. Both maps in each homotopy are the
maps constructed from the actual distinguished functors above.
There is no cohomology, higher-limit, spectral-sequence, convergence,
collapse or edge-isomorphism field in this literature input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (p : ℕ) (L : F.CentricLinkingSystem)

structure BLOSubgroupComparisonInput [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) where
  comparisonInverse : ∀ P : L.Object,
    L.subgroupDiagram.obj (L.orbitProjection.obj P) ⟶ L.groupClassifyingSpace P
  comparison_left : ∀ P, TopCat.Homotopy
    (L.subgroupComparison P ≫ comparisonInverse P) (𝟙 (L.groupClassifyingSpace P))
  comparison_right : ∀ P, TopCat.Homotopy
    (comparisonInverse P ≫ L.subgroupComparison P)
      (𝟙 (L.subgroupDiagram.obj (L.orbitProjection.obj P)))
  comparison_naturality : ∀ {P Q : L.Object} (f : P ⟶ Q), TopCat.Homotopy
    (L.subgroupComparison P ≫ L.subgroupDiagram.map (L.orbitProjection.map f))
    (L.classifyingMapOfProjection f ≫ L.subgroupComparison Q)

variable {p L} [Fact p.Prime] {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.BLOSubgroupComparisonInput p hS sat)
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupCohomologyComparison (P : L.Object) (n : ℕ) :
    SingularCohomology.cohomology R (L.subgroupDiagram.obj (L.orbitProjection.obj P)) A n ≅
      SingularCohomology.cohomology R (L.groupClassifyingSpace P) A n :=
  SingularCohomology.pullIsoOfHomotopyInverse R (L.subgroupComparison P)
    (I.comparisonInverse P) (I.comparison_left P) (I.comparison_right P) A n

theorem subgroupCohomologyComparison_naturality {P Q : L.Object} (f : P ⟶ Q) (n : ℕ) :
    SingularCohomology.pull R (L.subgroupDiagram.map (L.orbitProjection.map f)) A n ≫
        (subgroupCohomologyComparison I R A P n).hom =
      (subgroupCohomologyComparison I R A Q n).hom ≫
        SingularCohomology.pull R (L.classifyingMapOfProjection f) A n := by
  change SingularCohomology.pull R _ A n ≫ SingularCohomology.pull R _ A n =
    SingularCohomology.pull R _ A n ≫ SingularCohomology.pull R _ A n
  rw [← SingularCohomology.pull_comp, ← SingularCohomology.pull_comp]
  exact SingularCohomology.pull_eq_of_homotopy R (I.comparison_naturality f) A n

theorem subgroupComparison_restriction_component (P : L.Object) (n : ℕ) :
    SingularCohomology.pull R (L.subgroupDiagramForget (L.orbitProjection.obj P)) A n ≫
        (subgroupCohomologyComparison I R A P n).hom =
      SingularCohomology.pull R (L.subgroupClassifyingMap P) A n := by
  change SingularCohomology.pull R _ A n ≫ SingularCohomology.pull R _ A n = _
  rw [← SingularCohomology.pull_comp, L.subgroupComparison_comp_forget]

end Sharpness.FusionSystem.CentricLinkingSystem
