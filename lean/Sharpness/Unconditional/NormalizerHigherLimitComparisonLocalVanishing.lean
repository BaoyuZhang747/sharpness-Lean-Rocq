import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalCoefficient
import Sharpness.Unconditional.NormalizerOrbitLocalEquivalence

/-! The actual same-chain pair-category fibre has vanishing positive
higher limits for ordinary cohomology, after choosing the constructed
Sylow representative. The coefficient is pulled from the ambient centric
orbit category by its actual forgetful functor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def normalizerAtChainForget (σ : F.CentricChain) : F.NormalizerOrbitAtChain σ ⥤ F.CentricOrbit where
  obj P := P.obj.centric
  map f := f.hom.val

def normalizerAtChainCohomologyCoefficient (R A : Type u) [CommRing R]
    [AddCommGroup A] [Module R A] (σ : F.CentricChain) (n : ℕ) :
    CoefficientCategory R (F.NormalizerOrbitAtChain σ) :=
  (F.normalizerAtChainForget σ).op ⋙ F.cohomologyCoefficient (R := R) (A := A) n

namespace CentricLinkingSystem
variable {F} (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {R A : Type u} [CommRing R] [AddCommGroup A] [Module R A]

def normalizerLocalPairCohomologyIso (σ : F.CentricChain) (n : ℕ) :
    (L.normalizerLocalPairEquivalence p hS sat σ).functor.op ⋙
      F.normalizerAtChainCohomologyCoefficient R A σ n ≅
        L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat σ n :=
  Iso.refl _

/-- Exact same-chain category, exact ambient coefficient, and native higher
limits, including degree zero. No comma-cofinality conclusion is used. -/
def normalizerRepresentativeAtChainHigherLimitIso (d : F.NormalizerCategory) (n i : ℕ) :
    higherLimit (F.normalizerAtChainCohomologyCoefficient R A
      (L.normalizerSylowRepresentative p hS sat d) n) i ≅
      higherLimit ((L.chainNormalizerFusion
        (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
          (R := R) (A := A) n) i :=
  higherLimitEquivalenceIso R
    (L.normalizerLocalPairEquivalence p hS sat (L.normalizerSylowRepresentative p hS sat d))
    (F.normalizerAtChainCohomologyCoefficient R A (L.normalizerSylowRepresentative p hS sat d) n) i ≪≫
  higherLimitIso (L.normalizerLocalPairCohomologyIso p hS sat
    (L.normalizerSylowRepresentative p hS sat d) n) i ≪≫
  L.normalizerRepresentativeAmbientHigherLimitIso p hS sat d n i

variable (k : Type u) [Field k] [CharP k p]
    {B : Type u} [AddCommGroup B] [Module k B]

theorem normalizerRepresentativeAmbientHigherLimit_isZero
    (d : F.NormalizerCategory) (n i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero (higherLimit
      (L.normalizerAmbientCohomologyCoefficient (R := k) (A := B) p hS sat
        (L.normalizerSylowRepresentative p hS sat d) n) i) :=
  CategoryTheory.Limits.IsZero.of_iso
    ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomology_acyclic_unconditional
      p k (hS.to_subgroup _) (L.normalizerRepresentativeFusion_saturated p hS sat d) n i hi)
    (L.normalizerRepresentativeAmbientHigherLimitIso p hS sat d n i)

theorem normalizerRepresentativeAtChainHigherLimit_isZero
    (d : F.NormalizerCategory) (n i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero (higherLimit
      (F.normalizerAtChainCohomologyCoefficient k B
        (L.normalizerSylowRepresentative p hS sat d) n) i) :=
  CategoryTheory.Limits.IsZero.of_iso
    ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomology_acyclic_unconditional
      p k (hS.to_subgroup _) (L.normalizerRepresentativeFusion_saturated p hS sat d) n i hi)
    (L.normalizerRepresentativeAtChainHigherLimitIso p hS sat d n i)

end CentricLinkingSystem
end Sharpness.FusionSystem
