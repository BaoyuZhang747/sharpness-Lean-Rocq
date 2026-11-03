import Sharpness.Unconditional.NormalizerSubdivisionCommaLifts
import Sharpness.Unconditional.NormalizerSubdivisionCommaTorsor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The actual left adjoint to the chain-automorphism comparison into
the normalizer comma category. No geometric or homological comparison
is assumed in this construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerCommaBaseArrow (σ : F.CentricChain)
    (X : CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ)) :
    X.left ⟶ L.normalizerSubdivisionObj σ :=
  Classical.choice (L.normalizerSubdivision_exists_of_subconjugate X.left.chain σ
    (leOfHom X.hom))

def normalizerCommaBase (σ : F.CentricChain)
    (X : CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ)) :
    X ⟶ (L.normalizerSubdivisionChainComparison σ).obj (SingleObj.star (L.ChainAut σ)) :=
  CostructuredArrow.homMk (L.normalizerCommaBaseArrow σ X) (by apply Subsingleton.elim)

def normalizerCommaHomEquiv (σ : F.CentricChain)
    (X : CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ))
    (Y : SingleObj (L.ChainAut σ)) :
    (SingleObj.star (L.ChainAut σ) ⟶ Y) ≃
      (X ⟶ (L.normalizerSubdivisionChainComparison σ).obj Y) :=
  Equiv.ofBijective
    (fun a => L.normalizerCommaBase σ X ≫ (L.normalizerSubdivisionChainComparison σ).map a) (by
      constructor
      · intro a b hab
        exact L.normalizerSubdivision_post_injective (L.normalizerCommaBaseArrow σ X)
          (congrArg (fun t => t.left) hab)
      · intro f
        obtain ⟨a, ha, _⟩ := L.normalizerSubdivision_hom_torsor
          (L.normalizerCommaBaseArrow σ X) f.left
        exact ⟨a, CostructuredArrow.hom_ext _ _ ha⟩)

theorem normalizerCommaHomEquiv_naturality (σ : F.CentricChain)
    (X : CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ))
    (Y Y' : SingleObj (L.ChainAut σ)) (g : Y ⟶ Y')
    (h : SingleObj.star (L.ChainAut σ) ⟶ Y) :
    L.normalizerCommaHomEquiv σ X Y' (h ≫ g) =
      L.normalizerCommaHomEquiv σ X Y h ≫ (L.normalizerSubdivisionChainComparison σ).map g := by
  change L.normalizerCommaBase σ X ≫
    (L.normalizerSubdivisionChainComparison σ).map (h ≫ g) = _
  rw [(L.normalizerSubdivisionChainComparison σ).map_comp]
  exact (Category.assoc _ _ _).symm

def normalizerCommaReflection (σ : F.CentricChain) :
    CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ) ⥤
      SingleObj (L.ChainAut σ) :=
  Adjunction.leftAdjointOfEquiv (L.normalizerCommaHomEquiv σ)
    (L.normalizerCommaHomEquiv_naturality σ)

def normalizerCommaAdjunction (σ : F.CentricChain) :
    L.normalizerCommaReflection σ ⊣ L.normalizerSubdivisionChainComparison σ :=
  Adjunction.adjunctionOfEquivLeft (L.normalizerCommaHomEquiv σ)
    (L.normalizerCommaHomEquiv_naturality σ)

end Sharpness.FusionSystem.CentricLinkingSystem
