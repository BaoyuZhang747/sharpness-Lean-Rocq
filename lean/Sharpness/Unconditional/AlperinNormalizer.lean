import Sharpness.FullyNormalized

/-! The normalizer extension used in the descending-order proof of Alperin
generation. The Sylow adjustment is performed in the actual fusion
automorphism groups. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open scoped Pointwise

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- Conjugation of fusion automorphisms along a fusion isomorphism. -/
def alperinAutTransport {P Q : Subgroup S} (e : P ≃* Q)
    (he : F.IsHom e.toMonoidHom) :
    F.automorphismSubgroup P ≃* F.automorphismSubgroup Q where
  toFun a := ⟨e.symm.trans (a.val.trans e),
    F.comp_mem _ _ (F.comp_mem _ _ (F.inverse_mem e he) a.property) he⟩
  invFun a := ⟨e.trans (a.val.trans e.symm),
    F.comp_mem _ _ (F.comp_mem _ _ he a.property) (F.inverse_mem e he)⟩
  left_inv a := by
    apply Subtype.ext
    ext x
    simp
  right_inv a := by
    apply Subtype.ext
    ext x
    simp
  map_mul' a b := by
    apply Subtype.ext
    ext x
    simp

@[simp] theorem alperinAutTransport_apply {P Q : Subgroup S} (e : P ≃* Q)
    (he : F.IsHom e.toMonoidHom) (a : F.automorphismSubgroup P) (q : Q) :
    (F.alperinAutTransport e he a).val q = e (a.val (e.symm q)) := rfl

theorem alperinAutTransport_trans {P Q : Subgroup S} (e : P ≃* Q)
    (he : F.IsHom e.toMonoidHom) (a : F.automorphismSubgroup Q)
    (b : F.automorphismSubgroup P) :
    F.alperinAutTransport (e.trans a.val) (F.comp_mem _ _ he a.property) b =
      a * F.alperinAutTransport e he b * a⁻¹ := by
  apply Subtype.ext
  ext x
  rfl

/-- A fusion isomorphism to a fully normalized subgroup can be adjusted
by an automorphism of its target so that its extension domain is the
entire source normalizer. -/
theorem exists_iso_extensionDomain_eq_normalizer_of_sylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom)
    (hSylow : ¬ p ∣ (F.innerSylowSubgroup Q).relIndex (F.automorphismSubgroup Q)) :
    ∃ (ψ : P ≃* Q) (hψ : F.IsHom ψ.toMonoidHom),
      F.extensionDomain ψ = (Subgroup.normalizer (P : Set S) : Set S) := by
  let AP := F.automorphismSubgroup P
  let AQ := F.automorphismSubgroup Q
  let HP := (F.innerSylowSubgroup P).subgroupOf AP
  let HQ := (F.innerSylowSubgroup Q).subgroupOf AQ
  have hpP : IsPGroup p HP := (F.conjugation_isPGroup p hS P).of_equiv
    (Subgroup.subgroupOfEquivOfLe (F.innerSylowSubgroup_le P)).symm
  have hpQ : IsPGroup p HQ := (F.conjugation_isPGroup p hS Q).of_equiv
    (Subgroup.subgroupOfEquivOfLe (F.innerSylowSubgroup_le Q)).symm
  let τ : AP ≃* AQ := F.alperinAutTransport e he
  let H : Subgroup AQ := HP.map τ.toMonoidHom
  have hpH : IsPGroup p H := hpP.map τ.toMonoidHom
  obtain ⟨T, hHT⟩ := hpH.exists_le_sylow
  let U : Sylow p AQ := hpQ.toSylow hSylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq AQ T U
  let ψ := e.trans a.val
  have hψ : F.IsHom ψ.toMonoidHom := F.comp_mem _ _ he a.property
  refine ⟨ψ, hψ, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl, _, _⟩
    exact n.property
  · intro x hx
    let n : Subgroup.normalizer (P : Set S) := ⟨x, hx⟩
    let b : AP := ⟨P.normalizerMonoidHom n, F.normalizerAut_allowed P n⟩
    have hb : b ∈ HP := ⟨n, rfl⟩
    have hbH : τ b ∈ H := ⟨b, hb, rfl⟩
    have hbT : τ b ∈ (T : Subgroup AQ) := hHT hbH
    have hsmul := Subgroup.smul_mem_pointwise_smul (τ b) (MulAut.conj a)
      (T : Subgroup AQ) hbT
    have hconj : a * τ b * a⁻¹ ∈ (U : Subgroup AQ) := by
      rw [← ha, Sylow.coe_subgroup_smul]
      simpa only [MulAut.smul_def, MulAut.conj_apply] using hsmul
    have htransport : F.alperinAutTransport ψ hψ b ∈ HQ := by
      rw [alperinAutTransport_trans]
      exact hconj
    obtain ⟨t, ht⟩ := htransport
    refine ⟨n, rfl, t, ?_⟩
    intro y
    have hy := congrArg (fun z : MulAut Q => z (ψ y)) ht
    change (Q.normalizerMonoidHom t) (ψ y) = ψ (b.val (ψ.symm (ψ y))) at hy
    simpa only [alperinAutTransport_apply, MulEquiv.symm_apply_apply] using hy.symm

theorem exists_iso_extensionDomain_eq_normalizer (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) (hQ : F.FullyNormalized Q) :
    ∃ (ψ : P ≃* Q) (hψ : F.IsHom ψ.toMonoidHom),
      F.extensionDomain ψ = (Subgroup.normalizer (P : Set S) : Set S) :=
  F.exists_iso_extensionDomain_eq_normalizer_of_sylow p hS e he
    (sat.fully_normalized Q hQ).2

/-- The resulting morphism on the source normalizer, with its prescribed
restriction to the original subgroup. -/
theorem exists_normalizer_extension_to_fullyNormalized (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) (hQ : F.FullyNormalized Q) :
    ∃ (ψ : P ≃* Q), F.IsHom ψ.toMonoidHom ∧
      ∃ f : Subgroup.normalizer (P : Set S) →* (⊤ : Subgroup S),
        F.IsHom f ∧ ∀ x : P,
          (f ⟨x.val, Subgroup.le_normalizer x.property⟩).val = (ψ x).val := by
  obtain ⟨ψ, hψ, hdom⟩ :=
    F.exists_iso_extensionDomain_eq_normalizer p hS sat e he hQ
  obtain ⟨N, hPN, hN, f, hf, hext⟩ :=
    sat.extension ψ hψ (sat.fully_normalized Q hQ).1
  have hnormalizer : Subgroup.normalizer (P : Set S) ≤ N := by
    intro x hx
    rw [← SetLike.mem_coe, hN, hdom]
    exact hx
  refine ⟨ψ, hψ, f.comp (subgroupInclusion _ N hnormalizer),
    F.comp_mem _ _ (F.inclusion_mem hnormalizer) hf, ?_⟩
  intro x
  exact hext x

end Sharpness.FusionSystem
