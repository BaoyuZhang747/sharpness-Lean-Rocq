import Sharpness.Unconditional.QuotientSaturation

/-! Lifting the exact extension domain from a central quotient when the
target preimage is fully normalized. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

@[simp] theorem quotientInducedEquiv_apply {A B : Subgroup (S ⧸ Z)}
    (e : F.quotientPreimage Z A ≃* F.quotientPreimage Z B)
    (he : F.IsHom e.toMonoidHom) (x : F.quotientPreimage Z A) :
    F.quotientInducedEquiv hZ e he (F.subgroupProjection Z A x) =
      F.subgroupProjection Z B (e x) := F.quotientInducedHom_apply hZ _ x

omit [Finite S] in
@[simp] theorem quotientNormalizerMap_apply (A : Subgroup (S ⧸ Z))
    (n : Subgroup.normalizer (F.quotientPreimage Z A : Set S))
    (x : F.quotientPreimage Z A) :
    A.normalizerMonoidHom (F.quotientNormalizerMap A n) (F.subgroupProjection Z A x) =
      F.subgroupProjection Z A ((F.quotientPreimage Z A).normalizerMonoidHom n x) := by
  apply Subtype.ext
  change (QuotientGroup.mk' Z) n.val * (QuotientGroup.mk' Z) x.val *
      ((QuotientGroup.mk' Z) n.val)⁻¹ = (QuotientGroup.mk' Z) (n.val * x.val * n.val⁻¹)
  simp only [map_mul, map_inv]

theorem quotient_extensionDomain_preimage (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {A B : Subgroup (S ⧸ Z)}
    (e : F.quotientPreimage Z A ≃* F.quotientPreimage Z B)
    (he : F.IsHom e.toMonoidHom)
    (hB : F.FullyNormalized (F.quotientPreimage Z B)) :
    (QuotientGroup.mk' Z) ⁻¹'
        (F.centralQuotient hZ).extensionDomain (F.quotientInducedEquiv hZ e he) =
      F.extensionDomain e := by
  ext s
  constructor
  · rintro ⟨nbar, hnbar, tbar, hrel⟩
    have hn : s ∈ Subgroup.normalizer (F.quotientPreimage Z A : Set S) := by
      rw [← F.quotientPreimage_normalizer]
      change (QuotientGroup.mk' Z) s ∈ Subgroup.normalizer (A : Set (S ⧸ Z))
      rw [← hnbar]
      exact nbar.property
    let n : Subgroup.normalizer (F.quotientPreimage Z A : Set S) := ⟨s, hn⟩
    have hnm : F.quotientNormalizerMap A n = nbar := Subtype.ext hnbar.symm
    obtain ⟨t, ht⟩ := F.quotientNormalizerMap_surjective B tbar
    let a : F.automorphismSubgroup (F.quotientPreimage Z B) :=
      ⟨e.symm.trans (((F.quotientPreimage Z A).normalizerMonoidHom n).trans e),
        F.comp_mem _ _ (F.comp_mem _ _ (F.inverse_mem e he)
          (F.normalizerAut_allowed _ n)) he⟩
    let b : F.automorphismSubgroup (F.quotientPreimage Z B) :=
      ⟨(F.quotientPreimage Z B).normalizerMonoidHom t, F.normalizerAut_allowed _ t⟩
    have hab : F.centralQuotientAutMap hZ B a = F.centralQuotientAutMap hZ B b := by
      rw [F.centralQuotientAutMap_normalizer]
      apply Subtype.ext
      apply MulEquiv.ext
      intro q
      obtain ⟨y, rfl⟩ := F.subgroupProjection_surjective Z B q
      change F.quotientInducedHom hZ _ (F.subgroupProjection Z B y) = _
      rw [F.quotientInducedHom_apply, F.quotientNormalizerMap_apply]
      have h := hrel (F.subgroupProjection Z A (e.symm y))
      rw [← hnm, ← ht, F.quotientNormalizerMap_apply,
        F.quotientInducedEquiv_apply, F.quotientInducedEquiv_apply,
        e.apply_symm_apply, F.quotientNormalizerMap_apply] at h
      exact h
    have hk : a * b⁻¹ ∈ (F.centralQuotientAutMap hZ B).ker := by
      change F.centralQuotientAutMap hZ B (a * b⁻¹) = 1
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hinner := F.centralQuotientAutMap_ker_le_innerSylow hZ p hS sat B hB hk
    have hb : b ∈ (F.innerSylowSubgroup (F.quotientPreimage Z B)).subgroupOf
        (F.automorphismSubgroup (F.quotientPreimage Z B)) := ⟨t, rfl⟩
    have ha := ((F.innerSylowSubgroup (F.quotientPreimage Z B)).subgroupOf
      (F.automorphismSubgroup (F.quotientPreimage Z B))).mul_mem hinner hb
    rw [inv_mul_cancel_right] at ha
    obtain ⟨t', ht'⟩ := ha
    refine ⟨n, rfl, t', ?_⟩
    intro x
    have hx := congrArg (fun f : MulAut (F.quotientPreimage Z B) => f (e x)) ht'
    change (F.quotientPreimage Z B).normalizerMonoidHom t' (e x) =
      e ((F.quotientPreimage Z A).normalizerMonoidHom n (e.symm (e x))) at hx
    simpa only [e.symm_apply_apply] using hx.symm
  · rintro ⟨n, rfl, t, hrel⟩
    refine ⟨F.quotientNormalizerMap A n, rfl, F.quotientNormalizerMap B t, ?_⟩
    intro q
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A q
    rw [F.quotientNormalizerMap_apply, F.quotientInducedEquiv_apply,
      F.quotientInducedEquiv_apply, F.quotientNormalizerMap_apply, hrel x]

theorem centralQuotient_extension_fullyNormalized (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {A B : Subgroup (S ⧸ Z)} (e : A ≃* B)
    (he : (F.centralQuotient hZ).IsHom e.toMonoidHom)
    (hB : (F.centralQuotient hZ).FullyNormalized B) :
    ∃ (N : Subgroup (S ⧸ Z)) (hAN : A ≤ N),
      (N : Set (S ⧸ Z)) = (F.centralQuotient hZ).extensionDomain e ∧
        ∃ f : N →* (⊤ : Subgroup (S ⧸ Z)), (F.centralQuotient hZ).IsHom f ∧
          ∀ x : A, (f ⟨x.val, hAN x.property⟩).val = (e x).val := by
  obtain ⟨e', he', heq⟩ := F.quotient_iso_has_lift hZ e he
  have hPB := F.quotientPreimage_fullyNormalized hZ B hB
  obtain ⟨N, hPN, hN, f, hf, hext⟩ :=
    sat.extension e' he' (sat.fully_normalized _ hPB).1
  have hZN : Z ≤ N := (QuotientGroup.le_comap_mk' Z A).trans hPN
  let C := N.map (QuotientGroup.mk' Z)
  have hC : F.quotientPreimage Z C = N := F.quotientPreimage_map hZN
  have hT : F.quotientPreimage Z (⊤ : Subgroup (S ⧸ Z)) = ⊤ := Subgroup.comap_top _
  let f' : F.quotientPreimage Z C →*
      F.quotientPreimage Z (⊤ : Subgroup (S ⧸ Z)) :=
    (MulEquiv.subgroupCongr hT.symm).toMonoidHom.comp
      (f.comp (MulEquiv.subgroupCongr hC).toMonoidHom)
  have hf' : F.IsHom f' := F.comp_mem _ _
    (F.comp_mem _ _ (F.subgroupCongr_allowed hC) hf) (F.subgroupCongr_allowed hT.symm)
  have hAC : A ≤ C := by
    intro a ha
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z a
    have hxa : x ∈ F.quotientPreimage Z A := by
      change (QuotientGroup.mk' Z) x ∈ A
      rw [hx]
      exact ha
    exact ⟨x, hPN hxa, hx⟩
  refine ⟨C, hAC, ?_, F.quotientInducedHom hZ ⟨f', hf'⟩, ⟨⟨f', hf'⟩, rfl⟩, ?_⟩
  · ext a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z a
    have hxC : (QuotientGroup.mk' Z) x ∈ C ↔ x ∈ N := by
      change x ∈ F.quotientPreimage Z C ↔ x ∈ N
      rw [hC]
    have hxD : (QuotientGroup.mk' Z) x ∈ (F.centralQuotient hZ).extensionDomain e ↔
        x ∈ F.extensionDomain e' := by
      rw [← heq]
      exact Iff.of_eq (congrArg (fun T : Set S => x ∈ T)
        (F.quotient_extensionDomain_preimage hZ p hS sat e' he' hPB))
    change (QuotientGroup.mk' Z) x ∈ C ↔
      (QuotientGroup.mk' Z) x ∈ (F.centralQuotient hZ).extensionDomain e
    rw [hxC, hxD]
    change x ∈ (N : Set S) ↔ x ∈ F.extensionDomain e'
    rw [hN]
  · intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    let xC : F.quotientPreimage Z C := ⟨x.val, hC.symm ▸ hPN x.property⟩
    change (F.quotientInducedHom hZ ⟨f', hf'⟩ (F.subgroupProjection Z C xC)).val = _
    rw [F.quotientInducedHom_apply, ← heq, F.quotientInducedEquiv_apply]
    change (QuotientGroup.mk' Z) (f ⟨x.val, hPN x.property⟩).val =
      (QuotientGroup.mk' Z) (e' x).val
    rw [hext x]

end Sharpness.FusionSystem
