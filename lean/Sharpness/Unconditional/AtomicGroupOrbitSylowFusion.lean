import Sharpness.FullyNormalized
import Sharpness.FusionQuotientKernel

/-! The image of the ambient normalizer is Sylow in the orbit automorphism
group of a fully normalized fusion subgroup. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem automorphismToOrbitAut_map_innerSylow (Q : Subgroup S) :
    ((F.innerSylowSubgroup Q).subgroupOf (F.automorphismSubgroup Q)).map
        (F.automorphismToOrbitAut Q) = (F.normalizerToOrbitAut Q).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨n, hn⟩, rfl⟩
    have hb : b = ⟨Q.normalizerMonoidHom n, F.normalizerAut_allowed Q n⟩ :=
      Subtype.ext hn.symm
    exact ⟨n, by rw [hb]; rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨Q.normalizerMonoidHom n, F.normalizerAut_allowed Q n⟩, ⟨n, rfl⟩, rfl⟩

theorem normalizerToOrbitAut_range_isPGroup (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (Q : Subgroup S) :
    IsPGroup p (F.normalizerToOrbitAut Q).range :=
  (hS.to_subgroup (Subgroup.normalizer (Q : Set S))).of_surjective
    (F.normalizerToOrbitAut Q).rangeRestrict (F.normalizerToOrbitAut Q).rangeRestrict_surjective

theorem normalizerToOrbitAut_range_index (p : ℕ) (sat : F.Saturated p)
    (Q : Subgroup S) (hQ : F.FullyNormalized Q) :
    ¬ p ∣ (F.normalizerToOrbitAut Q).range.index := by
  rw [← F.automorphismToOrbitAut_map_innerSylow Q]
  intro h
  exact (sat.fully_normalized Q hQ).2
    (h.trans (Subgroup.index_map_dvd _ (F.automorphismToOrbitAut_surjective Q)))

def normalizerToOrbitAut_sylow (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) (Q : Subgroup S) (hQ : F.FullyNormalized Q) :
    Sylow p (Aut (F.toOrbit.obj ⟨Q⟩)) :=
  (F.normalizerToOrbitAut_range_isPGroup p hS Q).toSylow
    (F.normalizerToOrbitAut_range_index p sat Q hQ)

@[simp] theorem normalizerToOrbitAut_sylow_coe (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (Q : Subgroup S) (hQ : F.FullyNormalized Q) :
    (F.normalizerToOrbitAut_sylow p hS sat Q hQ : Subgroup (Aut (F.toOrbit.obj ⟨Q⟩))) =
      (F.normalizerToOrbitAut Q).range := rfl

end Sharpness.FusionSystem
