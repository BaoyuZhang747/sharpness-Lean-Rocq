import Sharpness.Unconditional.NormalizerOrbitProjectionCommaInclusion

/-! The opposite fixed-chain inclusion into the literal structured-arrow
category used by pointwise right Kan extension. Its right objects and
coefficient functor are identified without replacing the comma category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def normalizerAtChainToStructuredComma (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) :
    (F.NormalizerOrbitAtChain σ)ᵒᵖ ⥤ StructuredArrow (op d) F.normalizerOrbitPairProjection.op :=
  (F.normalizerAtChainToComma σ d hσ).op ⋙
    (costructuredArrowOpEquivalence F.normalizerOrbitPairProjection d).functor

@[simp] theorem normalizerAtChainToStructuredComma_obj_right (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    (A : (F.NormalizerOrbitAtChain σ)ᵒᵖ) :
    ((F.normalizerAtChainToStructuredComma σ d hσ).obj A).right = op A.unop.obj := rfl

@[simp] theorem normalizerAtChainToStructuredComma_obj_hom (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    (A : (F.NormalizerOrbitAtChain σ)ᵒᵖ) :
    ((F.normalizerAtChainToStructuredComma σ d hσ).obj A).hom =
      (eqToHom ((congrArg F.normalizerClass A.unop.property).trans hσ)).op := rfl

@[simp] theorem normalizerAtChainToStructuredComma_map_right (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    {A B : (F.NormalizerOrbitAtChain σ)ᵒᵖ} (f : A ⟶ B) :
    ((F.normalizerAtChainToStructuredComma σ d hσ).map f).right = f.unop.hom.op := rfl

theorem normalizerAtChainToStructuredComma_forget (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d) :
    F.normalizerAtChainToStructuredComma σ d hσ ⋙
      StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op = (F.normalizerAtChainForget σ).op := rfl

instance normalizerAtChainToStructuredComma_initial_of_final (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    [(F.normalizerAtChainToComma σ d hσ).Final] :
    (F.normalizerAtChainToStructuredComma σ d hσ).Initial := by
  dsimp [normalizerAtChainToStructuredComma]
  infer_instance

end Sharpness.FusionSystem
