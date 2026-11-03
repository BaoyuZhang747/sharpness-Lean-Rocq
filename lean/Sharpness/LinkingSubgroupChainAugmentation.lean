import Sharpness.SimplicialChainTotalAugmentation
import Sharpness.LinkingSubgroupAlexanderWhitneyComponents

/-! The actual total-chain augmentation to singular chains of |L|,
its genuine subgroup restriction components, and its equality after
Alexander–Whitney with the already constructed diagonal augmentation.
No geometric quasi-isomorphism is assumed or asserted here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

def subgroupChainCoconeColumn (i : SimplexCategory) :
    chainReplacementColumn (L.subgroupChainDiagram R) i ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  simplicialChainCoconeColumn L.subgroupSingularDiagram R L.subgroupSingularCocone i

theorem subgroupChainCoconeColumn_inclusion (i : SimplexCategory)
    (s : ComposableArrows F.CentricOrbit i.len) :
    chainReplacementInclusion (L.subgroupChainDiagram R) i s ≫ L.subgroupChainCoconeColumn R i =
      (SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s)) :=
  simplicialChainCoconeColumn_inclusion L.subgroupSingularDiagram R L.subgroupSingularCocone i s

def subgroupChainAugmentation : L.subgroupTotalChains R ⟶
    (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  simplicialChainTotalAugmentation L.subgroupSingularDiagram R L.subgroupSingularCocone

theorem subgroupChainAugmentation_f (n : ℕ) :
    (L.subgroupChainAugmentation R).f n =
      chainTotalProjection (L.subgroupChainBicomplex R) 0 n n (by omega) ≫
        (L.subgroupChainCoconeColumn R ⦋0⦌).f n := rfl

theorem subgroupChainAugmentation_zeroColumn (n : ℕ)
    (s : ComposableArrows F.CentricOrbit 0) :
    (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫
        (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n (by change 0+n=n; omega) ≫
        (L.subgroupChainAugmentation R).f n =
      ((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))).f n := by
  calc
    _ = (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫
        (((L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n
            (by change 0+n=n; omega) ≫
          chainTotalProjection (L.subgroupChainBicomplex R) 0 n n (by omega)) ≫
          (L.subgroupChainCoconeColumn R ⦋0⦌).f n) := by
      simp only [subgroupChainAugmentation_f, Category.assoc]
    _ = (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫
        (L.subgroupChainCoconeColumn R ⦋0⦌).f n := by
      exact (congrArg (fun t =>
          (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫
            (t ≫ (L.subgroupChainCoconeColumn R ⦋0⦌).f n))
        (chainTotalProjection_inclusion (L.subgroupChainBicomplex R) 0 n n (by omega))).trans
          (congrArg (fun t => (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫ t)
            (Category.id_comp ((L.subgroupChainCoconeColumn R ⦋0⦌).f n)))
    _ = _ := HomologicalComplex.congr_hom (L.subgroupChainCoconeColumn_inclusion R ⦋0⦌ s) n

theorem subgroupChainAugmentation_otherColumn (p q n : ℕ) (h : p+q=n) (hp : p≠0) :
    (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
      (L.subgroupChainAugmentation R).f n = 0 := by
  rw [subgroupChainAugmentation_f, ← Category.assoc,
    chainTotalProjection_other (L.subgroupChainBicomplex R) 0 n n p q (by omega) h hp, zero_comp]

theorem subgroupAlexanderWhitney_chainAugmentation (ez : EilenbergZilberInput.{u} R) :
    L.subgroupAlexanderWhitney R ez ≫ L.subgroupChainAugmentation R =
      L.subgroupSingularDiagonalChainMap R := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  rintro ⟨s, x⟩
  calc
    _ = (L.subgroupSingularDiagonal.ιChainComplex ⟨s, x⟩ ≫
        (L.subgroupAlexanderWhitney R ez).f n ≫
        chainTotalProjection (L.subgroupChainBicomplex R) 0 n n (by omega)) ≫
        (L.subgroupChainCoconeColumn R ⦋0⦌).f n := by
      simp only [HomologicalComplex.comp_f, subgroupChainAugmentation_f, Category.assoc]
    _ = ((L.subgroupSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌
          (ComposableArrows.mk₀ (chainHead s))).f n) ≫
        (L.subgroupChainCoconeColumn R ⦋0⦌).f n :=
      congrArg (fun t => t ≫ (L.subgroupChainCoconeColumn R ⦋0⦌).f n)
        (L.subgroupAlexanderWhitney_zeroColumn R ez n (by omega) s x)
    _ = (L.subgroupSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        ((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))).f n := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, subgroupChainCoconeColumn_inclusion]
      rfl
    _ = (TopCat.toSSet.obj L.classifyingSpace).ιChainComplex
        ((TopCat.toSSet.map (L.subgroupDiagramForget (chainHead s))).app (op ⦋n⦌) x) :=
      SSet.ι_chainComplexMap_f _ _ _ _ _
    _ = _ := (L.subgroupSingularDiagonalChainMap_simplex R n s x).symm

end Sharpness.FusionSystem.CentricLinkingSystem
