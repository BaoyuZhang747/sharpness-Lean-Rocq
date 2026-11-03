import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalCentric
import Sharpness.Unconditional.NormalizerCentricRadicalCollectionContainment
import Sharpness.Manuscript.QuotientIsomorphisms

/-! The ambient centric collection in the actual normalizer fusion system
contains all its centric radical subgroups. Restriction to that collection
therefore preserves every higher limit, with the actual inclusion functor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem ambientCentric_of_chainNormalizerCentricRadical (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (σ : F.CentricChain) (P : Subgroup σ.normalizerSubgroup)
    (hc : (L.chainNormalizerFusion σ).IsCentric P)
    (hr : (L.chainNormalizerFusion σ).IsRadical p P) :
    F.IsCentric (σ.normalizerAmbientSubgroup P) :=
  L.ambientCentric_of_chainBottomImage_le σ P
    (finiteGroupFusionAlong_normal_le_of_centric_radical p (hS.to_subgroup _)
      (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ)
      (L.chainBottomImage σ) (L.chainBottomImage_isPGroup p hS σ)
      (L.chainBottomImage_le_normalizerRange σ) P hc hr)

/-- Precisely the ambient F-centric subgroups of the chain normalizer. -/
def normalizerAmbientCollection (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain) :
    (L.chainNormalizerFusion σ).ComparisonCollection p where
  member P := F.IsCentric (σ.normalizerAmbientSubgroup P)
  centric := L.chainNormalizerCentric_of_ambientCentric p sat σ
  overgroup hP hPQ := F.centric_overgroup hP (Subgroup.map_mono hPQ)
  contains_centric_radical := L.ambientCentric_of_chainNormalizerCentricRadical p hS σ

theorem normalizerAmbientCollection_conjugate (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)
    {P Q : (L.chainNormalizerFusion σ).Orbit} (e : P ≅ Q)
    (hP : (L.normalizerAmbientCollection p hS sat σ).member P.as.subgroup) :
    (L.normalizerAmbientCollection p hS sat σ).member Q.as.subgroup :=
  L.ambientCentric_of_chainNormalizerIso p sat σ
    ((L.chainNormalizerFusion σ).groupEquivOfOrbitIso e)
    ((L.chainNormalizerFusion σ).groupEquivOfOrbitIso_allowed e) hP

/-- Every degree and every module-valued coefficient, over an arbitrary
commutative ring, on a fully K-normalized actual chain. -/
def normalizerAmbientCollectionHigherLimitIso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer)
    (R : Type u) [CommRing R]
    (M : CoefficientCategory R (L.chainNormalizerFusion σ).CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit
      ((L.normalizerAmbientCollection p hS sat σ).toCentric.op ⋙ M) n :=
  (L.chainNormalizerFusion σ).collectionRestrictionHigherLimitIso p (hS.to_subgroup _)
    (L.chainNormalizerFusion_saturated p hS sat σ hσ) R
    (L.normalizerAmbientCollection p hS sat σ)
    (L.normalizerAmbientCollection_conjugate p hS sat σ) M n

/-- The same comparison on each chosen normalizer representative, with
saturation and the Sylow property supplied by the proved construction. -/
def normalizerRepresentativeCollectionHigherLimitIso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory)
    (R : Type u) [CommRing R]
    (M : CoefficientCategory R
      (L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).CentricOrbit) (n : ℕ) :
    higherLimit M n ≅ higherLimit
      ((L.normalizerAmbientCollection p hS sat
        (L.normalizerSylowRepresentative p hS sat d)).toCentric.op ⋙ M) n :=
  (L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).collectionRestrictionHigherLimitIso
    p (hS.to_subgroup _) (L.normalizerRepresentativeFusion_saturated p hS sat d) R
    (L.normalizerAmbientCollection p hS sat (L.normalizerSylowRepresentative p hS sat d))
    (L.normalizerAmbientCollection_conjugate p hS sat (L.normalizerSylowRepresentative p hS sat d)) M n

end Sharpness.FusionSystem.CentricLinkingSystem
