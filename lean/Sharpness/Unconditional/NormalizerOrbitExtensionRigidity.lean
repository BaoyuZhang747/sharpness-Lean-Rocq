import Sharpness.Unconditional.PuigCentricEpi

/-! A fusion extension fixing a centric subgroup is conjugation by an element
of that subgroup. It therefore preserves its normalized subgroup objects.
This is used to control representatives in the finite normalizer route. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat

theorem centric_fixed_extension_conjugation
    {P R T : Subgroup S} (hP : F.IsCentric P) (hPR : P ≤ R)
    (f : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfix : ∀ x : P, (f.val ⟨x.val, hPR x.property⟩).val = x.val) :
    ∃ z : P, ∀ x : R, (f.val x).val = z.val⁻¹ * x.val * z.val := by
  let fTop : (⟨R⟩ : F.Object) ⟶ ⟨⊤⟩ := f ≫ F.inclusion le_top
  let iTop : (⟨R⟩ : F.Object) ⟶ ⟨⊤⟩ := F.inclusion le_top
  have hres : F.inclusion hPR ≫ iTop = F.inclusion hPR ≫ fTop := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact (hfix x).symm
  have he := F.centric_orbit_restriction_injective p hS sat hPR hP iTop fTop
    (congrArg F.toOrbit.map hres)
  obtain ⟨z, hz⟩ := (F.orbit_map_eq_iff iTop fTop).mp he
  have hz' (x : R) : (f.val x).val = z.val⁻¹ * x.val * z.val :=
    congrArg Subtype.val (hz x)
  have hc : z.val ∈ Subgroup.centralizer (P : Set S) := by
    intro y hy
    have heq : y = z.val⁻¹ * y * z.val :=
      (hfix ⟨y,hy⟩).symm.trans (hz' ⟨y,hPR hy⟩)
    have heq' := congrArg (fun a => z.val * a) heq
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using heq'.symm
  have hcent := hP P le_top (MulEquiv.refl P) (F.id_mem P)
  rw [inf_top_eq] at hcent
  exact ⟨⟨z.val,hcent hc⟩,hz'⟩

theorem centric_fixed_extension_preserves_normalized
    {P Q R T : Subgroup S} (hP : F.IsCentric P) (hPR : P ≤ R)
    (hN : P ≤ Subgroup.normalizer (Q : Set S))
    (f : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfix : ∀ x : P, (f.val ⟨x.val, hPR x.property⟩).val = x.val) :
    ∀ x : R, x.val ∈ Q ↔ (f.val x).val ∈ Q := by
  obtain ⟨z,hz⟩ := F.centric_fixed_extension_conjugation p hS sat hP hPR f hfix
  intro x
  rw [hz]
  exact (Subgroup.mem_normalizer_iff''.mp (hN z.property)) x.val

theorem centric_fixed_extension_normalized_image
    {P Q R T : Subgroup S} (hP : F.IsCentric P) (hPR : P ≤ R) (hQR : Q ≤ R)
    (hN : P ≤ Subgroup.normalizer (Q : Set S))
    (f : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfix : ∀ x : P, (f.val ⟨x.val, hPR x.property⟩).val = x.val) :
    (fun x : R => (f.val x).val) '' {x : R | x.val ∈ Q} = (Q : Set S) := by
  obtain ⟨z,hz⟩ := F.centric_fixed_extension_conjugation p hS sat hP hPR f hfix
  have hzn := hN z.property
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change (f.val x).val ∈ Q
    rw [hz]
    exact (Subgroup.mem_normalizer_iff''.mp hzn x.val).mp hx
  · intro hy
    have hx : z.val * y * z.val⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hzn y).mp hy
    refine ⟨⟨z.val*y*z.val⁻¹,hQR hx⟩,hx,?_⟩
    change (f.val ⟨z.val*y*z.val⁻¹,hQR hx⟩).val = y
    rw [hz]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end Sharpness.FusionSystem
