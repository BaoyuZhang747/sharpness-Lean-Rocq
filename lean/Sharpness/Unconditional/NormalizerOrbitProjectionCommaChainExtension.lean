import Sharpness.Unconditional.NormalizerOrbitProjectionCommaSylow
import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsRepresentatives
import Sharpness.Unconditional.Alperin

/-! A chain conjugacy can be adjusted inside the target stabilizer so that
it extends over the full simultaneous source normalizer. The selected
subgroup images remain the actual target chain entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

theorem CentricChain.Conjugacy.exists_normalizer_extension
    {κ σ : F.CentricChain} (c : CentricChain.Conjugacy κ σ)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (hSylow : ¬ p ∣ (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.index) :
    ∃ (N : Subgroup S) (hTop : κ.topSubgroup ≤ N), κ.normalizerSubgroup ≤ N ∧
      ∃ f : (⟨N⟩ : F.Object) ⟶ ⟨⊤⟩,
        ∀ i : Fin (κ.length + 1),
          (fun x : N => (f.val x).val) '' {x : N | x.val ∈ κ.subgroup i} =
            (σ.subgroup (c.indices i) : Set S) := by
  let e := F.alperinMulEquivOfIso c.topIso
  have he : F.IsHom e.toMonoidHom := c.topIso.hom.property
  have hK : σ.fusionStabilizer = F.kTransport e he κ.fusionStabilizer :=
    CentricChain.fusionStabilizer_eq_kTransport κ σ e he c.indices c.maps
  have hKT (a : κ.fusionStabilizer) :
      F.alperinAutTransport e he a.val ∈ σ.fusionStabilizer := by
    rw [hK]
    exact ⟨a.val, a.property, rfl⟩
  obtain ⟨a, N, hTop, hNorm, f, hf, hext⟩ := F.exists_stabilizer_adjusted_extension p hS sat
    e he (σ.centric (Fin.last σ.length)) κ.fusionStabilizer σ.fusionStabilizer hKT hSylow
  have hn : κ.normalizerSubgroup ≤ N := by
    rw [κ.normalizerSubgroup_eq_kNormalizer]
    exact hNorm
  refine ⟨N, hTop, hn, ⟨f, hf⟩, ?_⟩
  let ψ := e.trans a.val.val
  have hm (i : Fin (κ.length + 1)) (x : κ.topSubgroup) :
      x.val ∈ κ.subgroup i ↔ (ψ x).val ∈ σ.subgroup (c.indices i) :=
    (c.maps i x).trans (a.property (c.indices i) (e x))
  intro i
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let xt : κ.topSubgroup := ⟨x.val, κ.subgroup_mono (Fin.le_last i) hx⟩
    have hv : (f x).val = (ψ xt).val := hext xt
    change (f x).val ∈ σ.subgroup (c.indices i)
    rw [hv]
    exact (hm i xt).mp hx
  · intro hy
    let yt : σ.topSubgroup := ⟨y, σ.subgroup_mono (Fin.le_last _) hy⟩
    let xt : κ.topSubgroup := ψ.symm yt
    have hx : xt.val ∈ κ.subgroup i := (hm i xt).mpr (by
      change (ψ (ψ.symm yt)).val ∈ _
      rw [ψ.apply_symm_apply]
      exact hy)
    refine ⟨⟨xt.val, hTop xt.property⟩, hx, ?_⟩
    change (f ⟨xt.val, hTop xt.property⟩).val = y
    erw [hext]
    exact congrArg Subtype.val (ψ.apply_symm_apply yt)

namespace CentricLinkingSystem
variable (L : F.CentricLinkingSystem)

/-- The chosen actual Sylow chain representative has the corresponding
Sylow automizer inside its actual fusion stabilizer. -/
theorem normalizerRepresentative_automizer_sylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) :
    ¬ p ∣ (F.kNormalizerToAut (L.normalizerSylowRepresentative p hS sat d).topSubgroup
      (L.normalizerSylowRepresentative p hS sat d).fusionStabilizer).range.index := by
  let σ := L.normalizerSylowRepresentative p hS sat d
  have h := (L.normalizerRepresentativeSylow p hS sat d).not_dvd_index
  rw [L.normalizerRepresentativeSylow_range, L.chainNormalizerToAut_range,
    L.chainNormalizerSylowCandidate_index] at h
  exact h

end CentricLinkingSystem
end Sharpness.FusionSystem
