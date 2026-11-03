import Sharpness.Unconditional.BisimplicialRepresentable
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-! Explicit modelwise contractions. These constructions apply to products
of augmented simplicial sets with actual extra degeneracies, not to arbitrary
bisimplicial sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

def augmentedSSetProduct (P Q : SSet.Augmented.{u}) : SSet.Augmented.{u} where
  left := bisimplicialDiagonal (bisimplicialExternalProduct P.left Q.left)
  right := P.right × Q.right
  hom :=
    { app n := ↾fun z => (P.hom.app n z.1, Q.hom.app n z.2)
      naturality {a b} f := by
        apply ConcreteCategory.hom_ext
        intro z
        exact Prod.ext (congrArg (fun t => t z.1) (P.hom.naturality f))
          (congrArg (fun t => t z.2) (Q.hom.naturality f)) }

def augmentedSSetProductExtraDegeneracy (P Q : SSet.Augmented.{u})
    (eP : SimplicialObject.Augmented.ExtraDegeneracy P)
    (eQ : SimplicialObject.Augmented.ExtraDegeneracy Q) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedSSetProduct P Q) where
  s' := ↾fun z => (eP.s' z.1, eQ.s' z.2)
  s n := ↾fun z => (eP.s n z.1, eQ.s n z.2)
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) eP.s'_comp_ε)
      (congrArg (fun t => t z.2) eQ.s'_comp_ε)
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) eP.s₀_comp_δ₁)
      (congrArg (fun t => t z.2) eQ.s₀_comp_δ₁)
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_δ₀ n))
      (congrArg (fun t => t z.2) (eQ.s_comp_δ₀ n))
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_δ n i))
      (congrArg (fun t => t z.2) (eQ.s_comp_δ n i))
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Prod.ext (congrArg (fun t => t z.1) (eP.s_comp_σ n i))
      (congrArg (fun t => t z.2) (eQ.s_comp_σ n i))

def bisimplicialRepresentableAugmented (p q : ℕ) : SSet.Augmented.{u} :=
  augmentedSSetProduct (SSet.Augmented.stdSimplex.obj ⦋p⦌)
    (SSet.Augmented.stdSimplex.obj ⦋q⦌)

def bisimplicialRepresentableExtraDegeneracy (p q : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy (bisimplicialRepresentableAugmented.{u} p q) :=
  augmentedSSetProductExtraDegeneracy _ _
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋p⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋q⦌)

/-- A contraction of the actual model diagonal chains onto their augmentation
module in degree zero. All extra-degeneracy identities have been constructed. -/
def bisimplicialRepresentableDiagonalHomotopyEquiv (R : Type u) [CommRing R] (p q : ℕ) :
    HomotopyEquiv (bisimplicialDiagonalChains (bisimplicialRepresentable p q) R)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (((sigmaConst.obj (ModuleCat.of R R))).obj
          (bisimplicialRepresentableAugmented.{u} p q).right)) :=
  ((bisimplicialRepresentableExtraDegeneracy p q).map
    (sigmaConst.obj (ModuleCat.of R R))).homotopyEquiv

end Sharpness
