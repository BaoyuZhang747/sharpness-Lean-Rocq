import Sharpness.Unconditional.KNormalizationSylow
import Sharpness.Unconditional.FusionAtomicCentric

/-! A Sylow adjustment inside a prescribed fusion automorphism subgroup.
The adjusting automorphism remains in that subgroup, so it can preserve
all entries of a centric chain. The resulting extension contains the actual
source K-normalizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open scoped Pointwise
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem exists_stabilizer_adjustment_extensionDomain (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom)
    (K : Subgroup (F.automorphismSubgroup P))
    (T : Subgroup (F.automorphismSubgroup Q))
    (hKT : ∀ a : K, F.alperinAutTransport e he a.val ∈ T)
    (hSylow : ¬ p ∣ (F.kNormalizerToAut Q T).range.index) :
    ∃ a : T, (F.kNormalizer P K : Set S) ⊆ F.extensionDomain (e.trans a.val.val) := by
  let j : K →* T := ((F.alperinAutTransport e he).toMonoidHom.comp K.subtype).codRestrict T hKT
  let t : F.kNormalizer P K →* T := j.comp (F.kNormalizerToAut P K)
  have hpH : IsPGroup p t.range := (hS.to_subgroup _).of_surjective t.rangeRestrict
    t.rangeRestrict_surjective
  obtain ⟨V, hHV⟩ := hpH.exists_le_sylow
  let U : Sylow p T := (F.kNormalizerToAut_range_isPGroup p hS Q T).toSylow hSylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq T V U
  refine ⟨a, ?_⟩
  intro x hx
  let n : Subgroup.normalizer (P : Set S) := ⟨x, F.kNormalizer_le_normalizer P K hx⟩
  let b : F.kNormalizer P K := ⟨x, hx⟩
  have hbV : t b ∈ (V : Subgroup T) := hHV ⟨b, rfl⟩
  have hsmul := Subgroup.smul_mem_pointwise_smul (t b) (MulAut.conj a)
    (V : Subgroup T) hbV
  have hc : a * t b * a⁻¹ ∈ (F.kNormalizerToAut Q T).range := by
    change a * t b * a⁻¹ ∈ (U : Subgroup T)
    rw [← ha, Sylow.coe_subgroup_smul]
    simpa only [MulAut.smul_def, MulAut.conj_apply] using hsmul
  obtain ⟨z, hz⟩ := hc
  let z' : Subgroup.normalizer (Q : Set S) := ⟨z.val, F.kNormalizer_le_normalizer Q T z.property⟩
  let ψ := e.trans a.val.val
  have hψ : F.IsHom ψ.toMonoidHom := F.comp_mem _ _ he a.val.property
  have ht : F.alperinAutTransport ψ hψ (F.kNormalizerAction P n) =
      (F.kNormalizerToAut Q T z).val := by
    rw [F.alperinAutTransport_trans e he a.val (F.kNormalizerAction P n)]
    exact (congrArg Subtype.val hz).symm
  refine ⟨n, rfl, z', ?_⟩
  intro y
  have hy := congrArg (fun c : F.automorphismSubgroup Q => c.val (ψ y)) ht
  change ψ ((P.normalizerMonoidHom n) (ψ.symm (ψ y))) =
    (Q.normalizerMonoidHom z') (ψ y) at hy
  simpa only [MulEquiv.symm_apply_apply] using hy

/-- Receptivity of a centric target turns the Sylow adjustment into an actual
fusion morphism on a domain containing the source K-normalizer and source group. -/
theorem exists_stabilizer_adjusted_extension (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) (hQ : F.IsCentric Q)
    (K : Subgroup (F.automorphismSubgroup P))
    (T : Subgroup (F.automorphismSubgroup Q))
    (hKT : ∀ a : K, F.alperinAutTransport e he a.val ∈ T)
    (hSylow : ¬ p ∣ (F.kNormalizerToAut Q T).range.index) :
    ∃ (a : T) (N : Subgroup S) (hPN : P ≤ N), F.kNormalizer P K ≤ N ∧
      ∃ f : N →* (⊤ : Subgroup S), F.IsHom f ∧
        ∀ x : P, (f ⟨x.val, hPN x.property⟩).val = ((e.trans a.val.val) x).val := by
  obtain ⟨a, ha⟩ := F.exists_stabilizer_adjustment_extensionDomain p hS e he K T hKT hSylow
  have hψ : F.IsHom (e.trans a.val.val).toMonoidHom := F.comp_mem _ _ he a.val.property
  obtain ⟨N, hPN, hN, f, hf, hext⟩ := sat.extension (e.trans a.val.val) hψ
    (F.centric_fullyCentralized hQ)
  refine ⟨a, N, hPN, ?_, f, hf, hext⟩
  intro x hx
  change x ∈ (N : Set S)
  rw [hN]
  exact ha hx

end Sharpness.FusionSystem
