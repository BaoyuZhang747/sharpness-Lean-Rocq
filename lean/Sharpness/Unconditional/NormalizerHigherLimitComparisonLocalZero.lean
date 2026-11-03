import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalVanishing
import Sharpness.Unconditional.GroupCohomologyEmbeddingLimits

/-! The degree-zero local comparison with the actual compatible-tuple
group, with every representative and Sylow/index hypothesis constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p]
    {A : Type u} [AddCommGroup A] [Module k A]

theorem normalizerRepresentativeIndexIsUnit (d : F.NormalizerCategory) :
    IsUnit ((L.chainNormalizerToAut (L.normalizerSylowRepresentative p hS sat d)).range.index : k) := by
  rw [← L.normalizerRepresentativeSylow_range p hS sat d]
  exact OrdinaryCohomology.sylow_index_isUnit p k (L.normalizerRepresentativeSylow p hS sat d)

def normalizerRepresentativeCentricLimitIso (d : F.NormalizerCategory) (n : ℕ) :
    limit ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
      (R := k) (A := A) n) ≅
        OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) A n :=
  OrdinaryCohomology.embeddingCentricLimitIso
    (L.chainNormalizerToAut (L.normalizerSylowRepresentative p hS sat d))
    (L.chainNormalizerToAut_injective _) p (hS.to_subgroup _)
    (L.normalizerRepresentativeFusion_saturated p hS sat d)
    (L.normalizerRepresentativeIndexIsUnit p hS sat k d) n

def normalizerRepresentativeCentricHigherLimitZeroIso (d : F.NormalizerCategory) (n : ℕ) :
    higherLimit ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
      (R := k) (A := A) n) 0 ≅
        OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) A n :=
  OrdinaryCohomology.embeddingCentricHigherLimitZeroIso
    (L.chainNormalizerToAut (L.normalizerSylowRepresentative p hS sat d))
    (L.chainNormalizerToAut_injective _) p (hS.to_subgroup _)
    (L.normalizerRepresentativeFusion_saturated p hS sat d)
    (L.normalizerRepresentativeIndexIsUnit p hS sat k d) n

def normalizerRepresentativeAmbientHigherLimitZeroIso (d : F.NormalizerCategory) (n : ℕ) :
    higherLimit (L.normalizerAmbientCohomologyCoefficient (R := k) (A := A) p hS sat
      (L.normalizerSylowRepresentative p hS sat d) n) 0 ≅
        OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) A n :=
  L.normalizerRepresentativeAmbientHigherLimitIso p hS sat d n 0 ≪≫
    L.normalizerRepresentativeCentricHigherLimitZeroIso p hS sat k d n

def normalizerRepresentativeAtChainHigherLimitZeroIso (d : F.NormalizerCategory) (n : ℕ) :
    higherLimit (F.normalizerAtChainCohomologyCoefficient k A
      (L.normalizerSylowRepresentative p hS sat d) n) 0 ≅
        OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) A n :=
  L.normalizerRepresentativeAtChainHigherLimitIso p hS sat d n 0 ≪≫
    L.normalizerRepresentativeCentricHigherLimitZeroIso p hS sat k d n

theorem normalizerRepresentativeCentricLimitIso_inv_component
    (d : F.NormalizerCategory) (n : ℕ)
    (P : (L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).CentricOrbit) :
    (L.normalizerRepresentativeCentricLimitIso (A := A) p hS sat k d n).inv ≫
      limit.π ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
        (R := k) (A := A) n) (op P) =
      OrdinaryCohomology.pull
        ((L.chainNormalizerToAut (L.normalizerSylowRepresentative p hS sat d)).comp P.obj.as.subgroup.subtype) n :=
  OrdinaryCohomology.embeddingCentricLimitIso_inv_component _ _ p (hS.to_subgroup _)
    (L.normalizerRepresentativeFusion_saturated p hS sat d)
    (L.normalizerRepresentativeIndexIsUnit p hS sat k d) n P

end Sharpness.FusionSystem.CentricLinkingSystem
