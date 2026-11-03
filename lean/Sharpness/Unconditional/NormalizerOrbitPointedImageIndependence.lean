import Sharpness.Unconditional.NormalizerOrbitPointedImageBasic
import Sharpness.Unconditional.NormalizerOrbitExtensionRigidity

/-! Actual subgroup images are independent of the chosen extension and raw
orbit representative. This uses the proved centric restriction rigidity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerSubgroupExtension
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
  {P Q R T U : Subgroup S} {f g : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
include p hS sat

theorem image_le_of_orbitEq (a : F.NormalizerSubgroupExtension R T f)
    (b : F.NormalizerSubgroupExtension R U g)
    (hP : F.IsCentric P) (hQ : F.IsCentric Q)
    (hN : P ≤ Subgroup.normalizer (R : Set S))
    (hf : Function.Surjective f.val) (hfg : F.toOrbit.map f = F.toOrbit.map g) :
    b.image ≤ a.image := by
  let α := F.inclusion (sup_le a.acting_le a.subgroup_le) ≫ a.extension
  let β := F.inclusion (sup_le b.acting_le b.subgroup_le) ≫ b.extension
  have hα : F.inclusion (show P ≤ P ⊔ R from le_sup_left) ≫ α = f ≫ F.inclusion le_top := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact a.onActing x
  have hβ : F.inclusion (show P ≤ P ⊔ R from le_sup_left) ≫ β = g ≫ F.inclusion le_top := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact b.onActing x
  have he : F.toOrbit.map α = F.toOrbit.map β :=
    F.centric_orbit_restriction_injective p hS sat le_sup_left hP α β (by
      rw [hα, hβ, F.toOrbit.map_comp, F.toOrbit.map_comp, hfg])
  obtain ⟨z, hz⟩ := (F.orbit_map_eq_iff α β).mp he
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp hfg
  have hzact (x : P) : (g.val x).val = z.val⁻¹ * (f.val x).val * z.val := by
    have hx := congrArg Subtype.val (hz ⟨x.val, Subgroup.mem_sup_left x.property⟩)
    change (b.extension.val ⟨x.val, b.acting_le x.property⟩).val =
      z.val⁻¹ * (a.extension.val ⟨x.val, a.acting_le x.property⟩).val * z.val at hx
    rwa [a.onActing x, b.onActing x] at hx
  let w : S := z.val * r.val⁻¹
  have hwc : w ∈ Subgroup.centralizer (Q : Set S) := by
    intro y hy
    obtain ⟨x, hx⟩ := hf ⟨y, hy⟩
    have hxy : (f.val x).val = y := congrArg Subtype.val hx
    have h₁ : (g.val x).val = r.val⁻¹ * y * r.val := by
      have hh := congrArg Subtype.val (hr x)
      change (g.val x).val = r.val⁻¹ * (f.val x).val * r.val at hh
      rwa [hxy] at hh
    have h₂ : (g.val x).val = z.val⁻¹ * y * z.val := by rw [← hxy]; exact hzact x
    have hconj : r.val⁻¹ * y * r.val = z.val⁻¹ * y * z.val := h₁.symm.trans h₂
    have hfix : y = w⁻¹ * y * w := by
      dsimp [w]
      calc
        y = r.val * (r.val⁻¹ * y * r.val) * r.val⁻¹ := by group
        _ = r.val * (z.val⁻¹ * y * z.val) * r.val⁻¹ := by rw [hconj]
        _ = (z.val * r.val⁻¹)⁻¹ * y * (z.val * r.val⁻¹) := by group
    have hh := congrArg (fun v => w * v) hfix
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm
  have hcenter := hQ Q le_top (MulEquiv.refl Q) (F.id_mem Q)
  rw [inf_top_eq] at hcenter
  have hzQ : z.val ∈ Q := by
    have hh := Q.mul_mem (hcenter hwc) r.property
    simpa [w, mul_assoc] using hh
  intro y hy
  obtain ⟨x, hxy⟩ := (b.mem_image_iff y).mp hy
  have hpoint := congrArg Subtype.val (hz ⟨x.val, Subgroup.mem_sup_right x.property⟩)
  change (b.extension.val ⟨x.val, b.subgroup_le x.property⟩).val =
    z.val⁻¹ * (a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val * z.val at hpoint
  rw [← hxy, hpoint]
  exact (Subgroup.mem_normalizer_iff''.mp (a.image_normalizes hN hf hzQ) _).mp
    ((a.mem_image_iff _).mpr ⟨x, rfl⟩)

theorem image_eq_of_orbitEq (a : F.NormalizerSubgroupExtension R T f)
    (b : F.NormalizerSubgroupExtension R U g)
    (hP : F.IsCentric P) (hQ : F.IsCentric Q)
    (hN : P ≤ Subgroup.normalizer (R : Set S))
    (hf : Function.Surjective f.val) (hg : Function.Surjective g.val)
    (hfg : F.toOrbit.map f = F.toOrbit.map g) : a.image = b.image :=
  le_antisymm (image_le_of_orbitEq p hS sat b a hP hQ hN hg hfg.symm)
    (image_le_of_orbitEq p hS sat a b hP hQ hN hf hfg)

end Sharpness.FusionSystem.NormalizerSubgroupExtension
