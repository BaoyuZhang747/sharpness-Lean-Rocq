import Sharpness.ChainAutomorphismRestrictions

/-! Actual functors from chain automorphism groups to the linking
category, given by the first coordinate. For every actual subchain,
the specified inclusion gives the natural transformation comparing
this functor with tuple deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainAutomorphismFunctor (σ : F.CentricChain) : SingleObj (L.ChainAut σ) ⥤ L.Object :=
  SingleObj.functor ((Aut.toEnd (σ.linkingObject L 0)).comp (L.chainAutProjection σ 0))

theorem chainAutomorphismFunctor_map (σ : F.CentricChain) (a : L.ChainAut σ) :
    (L.chainAutomorphismFunctor σ).map (X := SingleObj.star (L.ChainAut σ))
      (Y := SingleObj.star (L.ChainAut σ)) a = (a.val 0).hom := rfl

def chainAutSubchainNaturality (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.chainAutomorphismFunctor σ ⟶
      (L.chainAutRestriction σ m e).toFunctor ⋙
        L.chainAutomorphismFunctor (σ.subchain m e) :=
  SingleObj.natTrans (L.chainInclusion σ (Fin.zero_le (e 0)))
    (fun a => a.property 0 (e 0) (Fin.zero_le (e 0)))

theorem chainAutSubchainNaturality_app (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    (L.chainAutSubchainNaturality σ m e).app (SingleObj.star (L.ChainAut σ)) =
      L.chainInclusion σ (Fin.zero_le (e 0)) := rfl

def chainClassifyingSpace (σ : F.CentricChain) : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve (SingleObj (L.ChainAut σ)))

def chainClassifyingMap (σ : F.CentricChain) : L.chainClassifyingSpace σ ⟶ L.classifyingSpace :=
  SSet.toTop.map (nerveMapSingleObj (L.ChainAut σ) (L.chainAutomorphismFunctor σ))

def chainRestrictionClassifyingMap (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.chainClassifyingSpace σ ⟶ L.chainClassifyingSpace (σ.subchain m e) :=
  SSet.toTop.map (CategoryTheory.nerveMap (L.chainAutRestriction σ m e).toFunctor)

end Sharpness.FusionSystem.CentricLinkingSystem
