import Sharpness.SimplicialChainTotalAugmentation
import Sharpness.NormalizerAlexanderWhitneyComponents

/-! The actual total-chain augmentation to singular chains of |L|,
its genuine normalizer restriction components, and its equality after
Alexander–Whitney with the already constructed diagonal augmentation.
No geometric quasi-isomorphism is assumed or asserted here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]

def normalizerChainCoconeColumn (i : SimplexCategory) :
    chainReplacementColumn (I.normalizerChainDiagram R) i ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  simplicialChainCoconeColumn I.normalizerSingularDiagram R I.normalizerSingularCocone i

theorem normalizerChainCoconeColumn_inclusion (i : SimplexCategory)
    (s : ComposableArrows F.NormalizerCategory i.len) :
    chainReplacementInclusion (I.normalizerChainDiagram R) i s ≫ I.normalizerChainCoconeColumn R i =
      (SingularCohomology.chainsFunctor R).map (I.normalizerDiagramForget (chainHead s)) :=
  simplicialChainCoconeColumn_inclusion I.normalizerSingularDiagram R I.normalizerSingularCocone i s

def normalizerChainAugmentation : I.normalizerTotalChains R ⟶
    (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  simplicialChainTotalAugmentation I.normalizerSingularDiagram R I.normalizerSingularCocone

theorem normalizerChainAugmentation_f (n : ℕ) :
    (I.normalizerChainAugmentation R).f n =
      chainTotalProjection (I.normalizerChainBicomplex R) 0 n n (by omega) ≫
        (I.normalizerChainCoconeColumn R ⦋0⦌).f n := rfl

theorem normalizerChainAugmentation_zeroColumn (n : ℕ)
    (s : ComposableArrows F.NormalizerCategory 0) :
    (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫
        (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n (by change 0+n=n; omega) ≫
        (I.normalizerChainAugmentation R).f n =
      ((SingularCohomology.chainsFunctor R).map (I.normalizerDiagramForget (chainHead s))).f n := by
  calc
    _ = (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫
        (((I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n
            (by change 0+n=n; omega) ≫
          chainTotalProjection (I.normalizerChainBicomplex R) 0 n n (by omega)) ≫
          (I.normalizerChainCoconeColumn R ⦋0⦌).f n) := by
      simp only [normalizerChainAugmentation_f, Category.assoc]
    _ = (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫
        (I.normalizerChainCoconeColumn R ⦋0⦌).f n := by
      exact (congrArg (fun t =>
          (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫
            (t ≫ (I.normalizerChainCoconeColumn R ⦋0⦌).f n))
        (chainTotalProjection_inclusion (I.normalizerChainBicomplex R) 0 n n (by omega))).trans
          (congrArg (fun t => (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫ t)
            (Category.id_comp ((I.normalizerChainCoconeColumn R ⦋0⦌).f n)))
    _ = _ := HomologicalComplex.congr_hom (I.normalizerChainCoconeColumn_inclusion R ⦋0⦌ s) n

theorem normalizerChainAugmentation_otherColumn (p q n : ℕ) (h : p+q=n) (hp : p≠0) :
    (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
      (I.normalizerChainAugmentation R).f n = 0 := by
  rw [normalizerChainAugmentation_f, ← Category.assoc,
    chainTotalProjection_other (I.normalizerChainBicomplex R) 0 n n p q (by omega) h hp, zero_comp]

theorem normalizerAlexanderWhitney_chainAugmentation (ez : EilenbergZilberInput.{u} R) :
    I.normalizerAlexanderWhitney R ez ≫ I.normalizerChainAugmentation R =
      I.normalizerSingularDiagonalChainMap R := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  rintro ⟨s, x⟩
  calc
    _ = (I.normalizerSingularDiagonal.ιChainComplex ⟨s, x⟩ ≫
        (I.normalizerAlexanderWhitney R ez).f n ≫
        chainTotalProjection (I.normalizerChainBicomplex R) 0 n n (by omega)) ≫
        (I.normalizerChainCoconeColumn R ⦋0⦌).f n := by
      simp only [HomologicalComplex.comp_f, normalizerChainAugmentation_f, Category.assoc]
    _ = ((I.normalizerSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌
          (ComposableArrows.mk₀ (chainHead s))).f n) ≫
        (I.normalizerChainCoconeColumn R ⦋0⦌).f n :=
      congrArg (fun t => t ≫ (I.normalizerChainCoconeColumn R ⦋0⦌).f n)
        (I.normalizerAlexanderWhitney_zeroColumn R ez n (by omega) s x)
    _ = (I.normalizerSingularDiagram.obj (chainHead s)).ιChainComplex x ≫
        ((SingularCohomology.chainsFunctor R).map (I.normalizerDiagramForget (chainHead s))).f n := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, normalizerChainCoconeColumn_inclusion]
      rfl
    _ = (TopCat.toSSet.obj L.classifyingSpace).ιChainComplex
        ((TopCat.toSSet.map (I.normalizerDiagramForget (chainHead s))).app (op ⦋n⦌) x) :=
      SSet.ι_chainComplexMap_f _ _ _ _ _
    _ = _ := (I.normalizerSingularDiagonalChainMap_simplex R n s x).symm

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
