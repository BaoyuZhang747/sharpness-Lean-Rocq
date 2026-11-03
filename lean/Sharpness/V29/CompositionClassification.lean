import Sharpness.V29.ReductionComposition
import Sharpness.V29.SimpleFunctor

/-! Identification of every actual factor of the constructed composition
series with the trace-summand simple Mackey functor.  This records the
classification identification used in Proposition 4.3 without assuming it. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory
open MackeyModule.V29

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime]
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (series : CompositionSeries M)
    (A : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (hA : A ∈ series.factors)

def compositionFactorMinimal : Subgroup S :=
  (F.simpleLabel A (series.factors_simple A hA)).Q.as.subgroup

theorem compositionFactorMinimal_isMinimal :
    F.IsMinimalSupport A (compositionFactorMinimal F p M series A hA) :=
  simpleLabel_isMinimalSupport F p A (series.factors_simple A hA)

def compositionFactorSimpleModel :
    MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape :=
  F.simpleFunctorAtMinimal A (series.factors_simple A hA)
    (compositionFactorMinimal F p M series A hA)
    (compositionFactorMinimal_isMinimal F p M series A hA)

/-- An isomorphism in the actual category of full Mackey modules, hence
compatible with restrictions, transfers and all orbit-category maps. -/
def compositionFactorIdentification :
    A ≅ compositionFactorSimpleModel F p M series A hA :=
  F.simpleFunctorAtMinimalIso A (series.factors_simple A hA)
    (compositionFactorMinimal F p M series A hA)
    (compositionFactorMinimal_isMinimal F p M series A hA)

end Sharpness.FusionSystem.V29
