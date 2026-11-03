import Sharpness.Unconditional.NormalizerOrbitProjectionCommaPointing
import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalVanishing
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Limits.Final

/-! The literal fixed-chain category embeds fully faithfully into the actual
projection comma category. Its acting-subgroup functor agrees exactly with
the local coefficient functor already used for the local higher limits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def normalizerAtChainToComma (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) :
    F.NormalizerOrbitAtChain σ ⥤ CostructuredArrow F.normalizerOrbitPairProjection d where
  obj A := CostructuredArrow.mk (eqToHom ((congrArg F.normalizerClass A.property).trans hσ))
  map f := CostructuredArrow.homMk f.hom (Subsingleton.elim _ _)
  map_id A := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

@[simp] theorem normalizerAtChainToComma_obj_left (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d) (A : F.NormalizerOrbitAtChain σ) :
    ((F.normalizerAtChainToComma σ d hσ).obj A).left = A.obj := rfl

@[simp] theorem normalizerAtChainToComma_map_left (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    {A B : F.NormalizerOrbitAtChain σ} (f : A ⟶ B) :
    ((F.normalizerAtChainToComma σ d hσ).map f).left = f.hom := rfl

instance normalizerAtChainToComma_faithful (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d) :
    (F.normalizerAtChainToComma σ d hσ).Faithful where
  map_injective h := InducedCategory.hom_ext (congrArg (fun f => f.left) h)

instance normalizerAtChainToComma_full (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d) :
    (F.normalizerAtChainToComma σ d hσ).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.left, CostructuredArrow.hom_ext _ _ rfl⟩

theorem normalizerAtChainToComma_forget (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d) :
    F.normalizerAtChainToComma σ d hσ ⋙
      CostructuredArrow.proj F.normalizerOrbitPairProjection d ⋙ F.normalizerOrbitPairForget =
        F.normalizerAtChainForget σ := rfl

/-- A raw pair arrow into a fixed-chain object defines a comma arrow: the
projection category is a preorder, so the required triangle is automatic. -/
def normalizerAtChainCommaArrow (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d)
    (X : CostructuredArrow F.normalizerOrbitPairProjection d)
    (A : F.NormalizerOrbitAtChain σ) (u : X.left ⟶ A.obj) :
    X ⟶ (F.normalizerAtChainToComma σ d hσ).obj A :=
  CostructuredArrow.homMk u (Subsingleton.elim _ _)

@[simp] theorem normalizerAtChainCommaArrow_left (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    (X : CostructuredArrow F.normalizerOrbitPairProjection d)
    (A : F.NormalizerOrbitAtChain σ) (u : X.left ⟶ A.obj) :
    (F.normalizerAtChainCommaArrow σ d hσ X A u).left = u := rfl

end Sharpness.FusionSystem
