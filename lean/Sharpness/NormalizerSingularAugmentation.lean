import Sharpness.NormalizerSingularReplacement
import Sharpness.SimplicialReplacementAugmentation
import Sharpness.NormalizerGeometryBase
import Sharpness.SingularChainsProjective

/-! The actual normalizer-forgetful maps give a simplicial augmentation
of the diagonal singular replacement to Sing(|L|), and hence an
actual map of nonnegative chain complexes. No quasi-isomorphism
property is assumed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

def normalizerSingularCocone : I.normalizerSingularDiagram ⟶
    (Functor.const F.NormalizerCategory).obj (TopCat.toSSet.obj L.classifyingSpace) where
  app P := TopCat.toSSet.map (I.normalizerDiagramForget P)
  naturality {P Q} f := by
    change TopCat.toSSet.map (I.normalizerDiagram.map f) ≫
        TopCat.toSSet.map (I.normalizerDiagramForget Q) =
      TopCat.toSSet.map (I.normalizerDiagramForget P) ≫ 𝟙 _
    rw [← TopCat.toSSet.map_comp, I.normalizerDiagramForget_naturality, Category.comp_id]

def normalizerSingularDiagonalAugmentation :
    I.normalizerSingularDiagonal ⟶ TopCat.toSSet.obj L.classifyingSpace :=
  simplicialReplacementDiagonalAugmentation I.normalizerSingularDiagram I.normalizerSingularCocone

theorem normalizerSingularDiagonalAugmentation_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows F.NormalizerCategory i.unop.len)
    (x : (TopCat.toSSet.obj (I.normalizerDiagram.obj (chainHead s))).obj i) :
    I.normalizerSingularDiagonalAugmentation.app i ⟨s, x⟩ =
      (TopCat.toSSet.map (I.normalizerDiagramForget (chainHead s))).app i x := rfl

def normalizerSingularDiagonalChainMap (R : Type u) [CommRing R] :
    I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R) ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  SSet.chainComplexMap I.normalizerSingularDiagonalAugmentation (ModuleCat.of R R)

theorem normalizerSingularDiagonalChainMap_simplex (R : Type u) [CommRing R]
    (n : ℕ) (s : ComposableArrows F.NormalizerCategory n)
    (x : (TopCat.toSSet.obj (I.normalizerDiagram.obj (chainHead s))).obj (op ⦋n⦌)) :
    I.normalizerSingularDiagonal.ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        (I.normalizerSingularDiagonalChainMap R).f n =
      (TopCat.toSSet.obj L.classifyingSpace).ιChainComplex
        ((TopCat.toSSet.map (I.normalizerDiagramForget (chainHead s))).app (op ⦋n⦌) x) :=
  SSet.ι_chainComplexMap_f I.normalizerSingularDiagonal (TopCat.toSSet.obj L.classifyingSpace)
    I.normalizerSingularDiagonalAugmentation (ModuleCat.of R R) ⟨s, x⟩

theorem normalizerSingularDiagonalChains_projective (R : Type u) [CommRing R] (n : ℕ) :
    Projective ((I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R I.normalizerSingularDiagonal n

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
