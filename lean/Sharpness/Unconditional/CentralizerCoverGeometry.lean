import Sharpness.Unconditional.CentralizerCoverFiberEquivalence
import Sharpness.Unconditional.CentralizerCoverOppositeFiber
import Sharpness.Unconditional.CentralizerCoverFinite

/-! The local centralizer coefficient diagrams are precisely the fiber
restrictions of the cover coefficient diagram, up to an explicit equivalence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u w
namespace Sharpness.FusionSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

def centralizedCoverToCentric : F.CentralizedCentralizerCover p ⥤ F.CentricOrbit :=
  F.centralizedCentralizerCoverInclusion p ⋙ F.centralizerCoverForget p

def centralizerCoverFibrationFiberEquivalence : C.system.CentricOrbitᵒᵖ ≌
    Functor.Fiber (F.centralizerCoverFibration p) E :=
  (F.centralizerCoverFiberEquivalence p hS sat E C).op.trans
    (oppositeFiberEquivalence (F.centralizerCoverProjection p) E)

def centralizerCoverFibrationFiberInclusionIso :
    (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).functor ⋙
        Functor.Fiber.fiberInclusion ⋙ (F.centralizedCoverToCentric p).op ≅
      (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
        (F.yalcinCentralizerCentricInput p hS sat E C).centric).op := Iso.refl _

def centralizerCoverFibrationFiberCoefficientIso
    {V : Type w} [Category V] (D : F.CentricOrbitᵒᵖ ⥤ V) :
    (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).functor ⋙
        Functor.Fiber.fiberInclusion ⋙ ((F.centralizedCoverToCentric p).op ⋙ D) ≅
      (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
        (F.yalcinCentralizerCentricInput p hS sat E C).centric).op ⋙ D :=
  Iso.refl _

end Sharpness.FusionSystem
