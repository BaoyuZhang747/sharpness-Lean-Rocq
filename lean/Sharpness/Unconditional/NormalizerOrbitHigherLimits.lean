import Sharpness.Unconditional.NormalizerOrbitCommaCofinality
import Sharpness.Unconditional.HomologicalCofinality

/-! Homological cofinality of the actual normalizer-pair forgetful functor,
natural in arbitrary coefficient diagrams and valid in every degree. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
  (R : Type u) [CommRing R]

def normalizerOrbitHigherLimitNatIso (n : ℕ) :
    higherLimitFunctor R F.CentricOrbit n ≅
      restrictionCoefficientFunctor R F.normalizerOrbitPairForget ⋙
        higherLimitFunctor R F.NormalizerOrbitPair n :=
  Unconditional.higherLimitNatIsoOfCommaAcyclicity R F.normalizerOrbitPairForget
    (fun P => F.normalizerOrbitUnderProjection_quasiIso p hS sat P R) n

def normalizerOrbitHigherLimitIso (M : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit (F.normalizerOrbitPairForget.op ⋙ M) n :=
  (F.normalizerOrbitHigherLimitNatIso p hS sat R n).app M

@[simp] theorem normalizerOrbitHigherLimitNatIso_app
    (M : CoefficientCategory R F.CentricOrbit) (n : ℕ) :
    (F.normalizerOrbitHigherLimitNatIso p hS sat R n).app M =
      F.normalizerOrbitHigherLimitIso p hS sat R M n := rfl

theorem normalizerOrbitHigherLimitIso_naturality
    {M N : CoefficientCategory R F.CentricOrbit} (f : M ⟶ N) (n : ℕ) :
    (higherLimitFunctor R F.CentricOrbit n).map f ≫
        (F.normalizerOrbitHigherLimitIso p hS sat R N n).hom =
      (F.normalizerOrbitHigherLimitIso p hS sat R M n).hom ≫
        (higherLimitFunctor R F.NormalizerOrbitPair n).map
          ((restrictionCoefficientFunctor R F.normalizerOrbitPairForget).map f) :=
  (F.normalizerOrbitHigherLimitNatIso p hS sat R n).hom.naturality f

end Sharpness.FusionSystem
