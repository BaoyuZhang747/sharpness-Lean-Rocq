import Sharpness.Unconditional.QuillenAChainsBaseProjection
import Sharpness.Unconditional.CostructuredDiagonalChainComparison
import Sharpness.Unconditional.NerveNaturalTransformation

/-! The two actual comma-diagonal projections commute with the original
functor up to the canonical comma-arrow chain homotopy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u vA uA

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

theorem costructuredDiagonalCommaMap_baseProjection :
    costructuredDiagonalCommaMap T ≫ nerveMap (Comma.snd T (𝟭 D)) =
      simplicialReplacementBaseDiagonal (costructuredNerveDiagram T) := by
  ext n x
  rfl

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasCoproducts.{u} A]

/-- The structural comma arrow supplies the actual comparison homotopy. -/
def costructuredDiagonalProjectionChainHomotopy (R : A) :
    Homotopy
      (SSet.chainComplexMap
        (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
          (costructuredNerveCocone T)) R ≫ SSet.chainComplexMap (nerveMap T) R)
      (SSet.chainComplexMap
        (simplicialReplacementBaseDiagonal (costructuredNerveDiagram T)) R) := by
  let J := (SSet.chainComplexFunctor A).obj R
  have h := (nerveNaturalTransformationChainHomotopy (Comma.natTrans T (𝟭 D)) R).compLeft
    (J.map (costructuredDiagonalCommaMap T))
  have hl : J.map (costructuredDiagonalCommaMap T) ≫
      J.map (nerveMap (Comma.fst T (𝟭 D) ⋙ T)) =
      J.map (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) ≫ J.map (nerveMap T) := by
    rw [← J.map_comp, ← J.map_comp]
    congr 1
  have hr : J.map (costructuredDiagonalCommaMap T) ≫
      J.map (nerveMap (Comma.snd T (𝟭 D) ⋙ 𝟭 D)) =
      J.map (simplicialReplacementBaseDiagonal (costructuredNerveDiagram T)) := by
    rw [← J.map_comp]
    exact congrArg J.map (costructuredDiagonalCommaMap_baseProjection T)
  change Homotopy (J.map (costructuredDiagonalCommaMap T) ≫
      J.map (nerveMap (Comma.fst T (𝟭 D) ⋙ T)))
    (J.map (costructuredDiagonalCommaMap T) ≫
      J.map (nerveMap (Comma.snd T (𝟭 D) ⋙ 𝟭 D))) at h
  rw [hl, hr] at h
  exact h

/-- Explicit comparison step: only the two constructed diagonal projections
are premises here; the desired functor map is not supplied as an input. -/
theorem nerveMap_quasiIso_of_costructuredDiagonal [CategoryWithHomology A] (R : A)
    (hAug : QuasiIso (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) R))
    (hBase : QuasiIso (SSet.chainComplexMap
      (simplicialReplacementBaseDiagonal (costructuredNerveDiagram T)) R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) R) := by
  letI := hAug
  letI := hBase
  haveI : QuasiIso (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) R ≫ SSet.chainComplexMap (nerveMap T) R) := by
    constructor
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap,
      (costructuredDiagonalProjectionChainHomotopy T R).homologyMap_eq n]
    infer_instance
  exact quasiIso_of_comp_left
    (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) R)
    (SSet.chainComplexMap (nerveMap T) R)

end Sharpness
