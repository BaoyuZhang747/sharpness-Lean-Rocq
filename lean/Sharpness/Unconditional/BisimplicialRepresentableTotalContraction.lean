import Sharpness.Unconditional.BisimplicialRepresentableContraction
import Sharpness.Unconditional.ChainTotalOuterSingle

/-! Actual horizontal and total contractions of representable bisimplicial models.
Only products equipped with constructed extra degeneracies are contracted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

def bisimplicialHorizontalAugmented (P Q : SSet.Augmented.{u}) :
    SimplicialObject.Augmented SSet.{u} where
  left := bisimplicialExternalProduct P.left Q.left
  right := (augmentedSSetProduct (SimplicialObject.Augmented.const.obj P.right) Q).left
  hom :=
    { app n := { app k := ↾fun z => (P.hom.app n z.1, z.2)
                 naturality := by intros; rfl }
      naturality {a b} f := by
        apply NatTrans.ext
        funext k
        apply ConcreteCategory.hom_ext
        intro z
        exact Prod.ext (congrArg (fun t => t z.1) (P.hom.naturality f)) rfl }

def bisimplicialHorizontalExtraDegeneracy (P Q : SSet.Augmented.{u})
    (eP : SimplicialObject.Augmented.ExtraDegeneracy P) :
    SimplicialObject.Augmented.ExtraDegeneracy (bisimplicialHorizontalAugmented P Q) where
  s' := { app k := ↾fun z => (eP.s' z.1, z.2)
          naturality := by intros; rfl }
  s n := { app k := ↾fun z => (eP.s n z.1, z.2)
           naturality := by intros; rfl }
  s'_comp_ε := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) eP.s'_comp_ε) rfl
  s₀_comp_δ₁ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) eP.s₀_comp_δ₁) rfl
  s_comp_δ₀ n := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_δ₀ n)) rfl
  s_comp_δ n i := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_δ n i)) rfl
  s_comp_σ n i := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_σ n i)) rfl

/-- Total chains of the actual external product contract to the augmentation
module when both factors have actual extra degeneracies. -/
def bisimplicialExternalProductTotalHomotopyEquiv (R : Type u) [CommRing R]
    (P Q : SSet.Augmented.{u})
    (eP : SimplicialObject.Augmented.ExtraDegeneracy P)
    (eQ : SimplicialObject.Augmented.ExtraDegeneracy Q) :
    HomotopyEquiv (bisimplicialTotalChains (bisimplicialExternalProduct P.left Q.left) R)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        ((sigmaConst.obj (ModuleCat.of R R)).obj (P.right × Q.right))) :=
  (chainTotalHorizontalHomotopyEquiv
    ((bisimplicialHorizontalExtraDegeneracy P Q eP).map (simplicialChainsFunctor R)).homotopyEquiv).trans
    ((HomotopyEquiv.ofIso (chainTotalOuterSingleIso _)).trans
      ((augmentedSSetProductExtraDegeneracy (SimplicialObject.Augmented.const.obj P.right) Q
        (SimplicialObject.Augmented.ExtraDegeneracy.const P.right) eQ).map
          (sigmaConst.obj (ModuleCat.of R R))).homotopyEquiv)

/-- A constructed contraction of every actual representable model total,
with precisely the same degree-zero augmentation module as its diagonal. -/
def bisimplicialRepresentableTotalHomotopyEquiv (R : Type u) [CommRing R] (p q : ℕ) :
    HomotopyEquiv (bisimplicialTotalChains (bisimplicialRepresentable p q) R)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        ((sigmaConst.obj (ModuleCat.of R R)).obj
          (bisimplicialRepresentableAugmented.{u} p q).right)) :=
  bisimplicialExternalProductTotalHomotopyEquiv R
    (SSet.Augmented.stdSimplex.obj ⦋p⦌) (SSet.Augmented.stdSimplex.obj ⦋q⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋p⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋q⦌)

end Sharpness
