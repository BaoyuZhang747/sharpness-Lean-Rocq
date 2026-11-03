import Sharpness.NormalizerChainCategory
import Sharpness.ChainAutomorphismFunctors
import Mathlib.CategoryTheory.Grothendieck

/-! The precise categorical data in Libman Theorem 5.1, on the actual
fusion-conjugacy quotient category and actual compatible-tuple groups.
Every comparison square specifies the actual tuple-deletion map.
Subchain squares are natural transformations, retaining the possibly
noninvertible inclusion of the initial subgroup into the selected one.
Conjugacy squares commute by a natural isomorphism. Requiring strict
equality there, together with the strict evaluation factorization,
would incorrectly make the first-coordinate automorphism map invariant
under every inner automorphism. The isomorphism supplies the homotopy
of the realized comparison maps; its canonical component is to be
verified when constructing these data.
This definition does not assert existence or any equivalence property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

structure LibmanNormalizerData where
  categoryDiagram : F.NormalizerCategory ⥤ Cat.{u,u}
  toLinking : Grothendieck categoryDiagram ⥤ L.Object
  chainComparison : ∀ σ : F.CentricChain,
    SingleObj (L.ChainAut σ) ⥤ (categoryDiagram.obj (F.normalizerClass σ))
  comparison_subchain : ∀ (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)),
    chainComparison σ ⋙ (categoryDiagram.map (F.normalizerSubchainArrow σ m e)).toFunctor ⟶
      (L.chainAutRestriction σ m e).toFunctor ⋙ chainComparison (σ.subchain m e)
  comparison_factorization : ∀ σ : F.CentricChain,
    chainComparison σ ⋙ Grothendieck.ι categoryDiagram (F.normalizerClass σ) ⋙ toLinking =
      L.chainAutomorphismFunctor σ
  comparison_conjugacy : ∀ (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ)
    (a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i))
    (_commutes : ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
      (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
        L.chainInclusion σ h ≫ (a j).hom)
    (φ : L.ChainAut σ ≃* L.ChainAut τ)
    (_coordinates : ∀ (g : L.ChainAut σ) (i : Fin (σ.length + 1)),
      ((φ g).val (c.indices i)).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom),
    chainComparison σ ⋙ (categoryDiagram.map
      (eqToHom ((F.normalizerClass_eq_iff σ τ).mpr ⟨c⟩))).toFunctor ≅
      φ.toMonoidHom.toFunctor ⋙ chainComparison τ

namespace LibmanNormalizerData
variable {L} (D : L.LibmanNormalizerData)

def diagram : F.NormalizerCategory ⥤ TopCat.{u} :=
  D.categoryDiagram ⋙ CategoryTheory.nerveFunctor ⋙ SSet.toTop

def grothendieckSpace : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve (Grothendieck D.categoryDiagram))

def grothendieckMap : D.grothendieckSpace ⟶ L.classifyingSpace :=
  SSet.toTop.map (CategoryTheory.nerveMap D.toLinking)

def chainComparisonMap (σ : F.CentricChain) :
    L.chainClassifyingSpace σ ⟶ D.diagram.obj (F.normalizerClass σ) :=
  SSet.toTop.map (nerveMapSingleObj (L.ChainAut σ) (D.chainComparison σ))

def fiberMap (d : F.NormalizerCategory) : D.diagram.obj d ⟶ D.grothendieckSpace :=
  SSet.toTop.map (CategoryTheory.nerveMap (Grothendieck.ι D.categoryDiagram d))

end LibmanNormalizerData
end Sharpness.FusionSystem.CentricLinkingSystem
