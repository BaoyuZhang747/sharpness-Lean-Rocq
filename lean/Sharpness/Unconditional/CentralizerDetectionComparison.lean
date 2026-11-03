import Sharpness.Unconditional.CentralizerCoverGeometry
import Sharpness.Unconditional.AtomicHigherLimits
import Sharpness.HigherLimitsEquivalence
import Sharpness.ExtZeroTarget

/-! Actual higher-limit comparisons for the centralizer cover and its fibers.
These use the concrete adjunction and equivalences, without a spectral-sequence
comparison assumption. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B] (e : A ≌ B)

def covariantCoefficientEquivalence : (B ⥤ ModuleCat.{u} R) ≌ (A ⥤ ModuleCat.{u} R) :=
  (Equivalence.congrLeft e).symm

instance covariantCoefficientEquivalence_additive :
    (covariantCoefficientEquivalence R e).functor.Additive where
  map_add := by
    intro D E f g
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance covariantCoefficientEquivalence_linear :
    (covariantCoefficientEquivalence R e).functor.Linear R where
  map_smul := by
    intro D E f r
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def covariantHigherLimitEquivalenceIso (D : B ⥤ ModuleCat.{u} R) (n : ℕ) :
    covariantHigherLimit R D n ≅ covariantHigherLimit R (e.functor ⋙ D) n :=
  extEquivalenceIso R (covariantCoefficientEquivalence R e)
    ((Functor.const B).obj (ModuleCat.of R R)) D n

namespace FusionSystem

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

/-- Restricting to the fully centralized cover preserves the original higher
limits: first use the section adjunction, then the concrete cover equivalence. -/
def centralizerCoverHigherLimitIso [Nontrivial S]
    (D : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    higherLimit D n ≅ covariantHigherLimit R ((F.centralizedCoverToCentric p).op ⋙ D) n :=
  higherLimitRightAdjointIso R (F.centralizerCoverSection p hS)
      (F.centralizerCoverForget p) (F.centralizerCoverSectionAdjunction p hS) D n ≪≫
    higherLimitEquivalenceIso R (F.centralizedCentralizerCoverEquivalence p sat)
      ((F.centralizerCoverForget p).op ⋙ D) n

/-- The covariant fiber derived limit is the ordinary higher limit on the
actual centralizer's centric orbit category, with its actual ambient restriction. -/
def centralizerFiberHigherLimitIso (E : F.ElementaryCategory p)
    (C : F.AKOCentralizerInput p hS sat E)
    (D : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    covariantHigherLimit R
      (Functor.Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        ((F.centralizedCoverToCentric p).op ⋙ D)) n ≅
      higherLimit
        ((F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
          (F.yalcinCentralizerCentricInput p hS sat E C).centric).op ⋙ D) n :=
  covariantHigherLimitEquivalenceIso R
    (F.centralizerCoverFibrationFiberEquivalence p hS sat E C) _ n

end FusionSystem
end Sharpness
