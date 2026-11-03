import Sharpness.Saturation

/-! A homomorphism extending an isomorphism on the whole source normalizer
maps into the target normalizer and intertwines its conjugation action. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] {P Q : Subgroup S}
    (e : Q ≃* P) (f : Subgroup.normalizer (Q : Set S) →* (⊤ : Subgroup S))
    (hfext : ∀ q : Q, (f ⟨q.val, Subgroup.le_normalizer q.property⟩).val = (e q).val)

include hfext

theorem normalizer_extension_conjugation
    (t : Subgroup.normalizer (Q : Set S)) (q : Q) :
    (e (Q.normalizerMonoidHom t q)).val =
      (f t).val * (e q).val * (f t).val⁻¹ := by
  have he : (⟨(Q.normalizerMonoidHom t q).val,
      Subgroup.le_normalizer (Q.normalizerMonoidHom t q).property⟩ :
      Subgroup.normalizer (Q : Set S)) =
        t * ⟨q.val, Subgroup.le_normalizer q.property⟩ * t⁻¹ := Subtype.ext rfl
  rw [← hfext (Q.normalizerMonoidHom t q), he]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hfext]

theorem normalizer_extension_mem_normalizer
    (t : Subgroup.normalizer (Q : Set S)) :
    (f t).val ∈ Subgroup.normalizer (P : Set S) := by
  have hmem (t : Subgroup.normalizer (Q : Set S)) (x : S) (hx : x ∈ P) :
      (f t).val * x * (f t).val⁻¹ ∈ P := by
    let q := e.symm ⟨x, hx⟩
    have hq : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    rw [← hq, ← normalizer_extension_conjugation e f hfext t q]
    exact (e (Q.normalizerMonoidHom t q)).property
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hmem t x, ?_⟩
  intro hx
  have hh := hmem t⁻¹ ((f t).val * x * (f t).val⁻¹) hx
  simpa [mul_assoc] using hh

theorem normalizer_extension_intertwines
    (t : Subgroup.normalizer (Q : Set S)) (q : Q) :
    e (Q.normalizerMonoidHom t q) =
      P.normalizerMonoidHom
        ⟨(f t).val, normalizer_extension_mem_normalizer e f hfext t⟩ (e q) := by
  apply Subtype.ext
  exact normalizer_extension_conjugation e f hfext t q

end Sharpness.FusionSystem
