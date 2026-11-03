import Sharpness.Unconditional.PuigCentricEpi

/-! Two centric fusion maps agreeing on a common subgroup extend jointly
over the join of its normalizers. Saturation supplies the joint extension;
centric rigidity identifies its two restrictions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem relativeNormalizer_fixes_restriction {R A T : Subgroup S} (hRA : R ≤ A)
    (f : (⟨A⟩ : F.Object) ⟶ ⟨T⟩) (n : (Subgroup.normalizer (R : Set S) ⊓ A : Subgroup S)) :
    F.normalizerToOrbitAut R ⟨n.val, n.property.1⟩ ∈
      F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hRA ≫ f)) := by
  change (F.normalizerToOrbitAut R ⟨n.val, n.property.1⟩).hom ≫
    F.toOrbit.map (F.inclusion hRA ≫ f) = _
  rw [F.toOrbit.map_comp, ← Category.assoc]
  have hh := F.relativeNormalizerToAut_fixes_inclusion hRA
    (⟨n.val, n.property.1, n.property.2⟩ : F.relativeNormalizer A R)
  exact congrArg (fun z => z ≫ F.toOrbit.map f) hh

/-- The prescribed maps on both normalizer intersections can be
amalgamated. Agreement is required only in the actual orbit category. -/
theorem centric_normalizer_amalgamation (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {R A B T : Subgroup S} (hRA : R ≤ A) (hRB : R ≤ B) (hR : F.IsCentric R)
    (f : (⟨A⟩ : F.Object) ⟶ ⟨T⟩) (g : (⟨B⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : F.toOrbit.map (F.inclusion hRA ≫ f) =
      F.toOrbit.map (F.inclusion hRB ≫ g)) :
    ∃ h : (⟨(Subgroup.normalizer (R : Set S) ⊓ A) ⊔
        (Subgroup.normalizer (R : Set S) ⊓ B)⟩ : F.Object) ⟶ ⟨T⟩,
      F.toOrbit.map (F.inclusion le_sup_left ≫ h) =
        F.toOrbit.map (F.inclusion inf_le_right ≫ f) ∧
      F.toOrbit.map (F.inclusion le_sup_right ≫ h) =
        F.toOrbit.map (F.inclusion inf_le_right ≫ g) := by
  let NA := Subgroup.normalizer (R : Set S) ⊓ A
  let NB := Subgroup.normalizer (R : Set S) ⊓ B
  let N := NA ⊔ NB
  let β : (⟨R⟩ : F.Object) ⟶ ⟨T⟩ := F.inclusion hRA ≫ f
  let H := F.orbitHomStabilizer (F.toOrbit.map β)
  have hRNA : R ≤ NA := le_inf Subgroup.le_normalizer hRA
  have hRNB : R ≤ NB := le_inf Subgroup.le_normalizer hRB
  have hRN : R ≤ N := hRNA.trans le_sup_left
  have hNN : N ≤ Subgroup.normalizer (R : Set S) := sup_le inf_le_left inf_le_left
  have hNAH : NA ≤ F.atomicNormalizerPreimage R H := by
    intro n hn
    exact (F.mem_atomicNormalizerPreimage R H n).mpr
      ⟨hn.1, F.relativeNormalizer_fixes_restriction hRA f ⟨n, hn⟩⟩
  have hNBH : NB ≤ F.atomicNormalizerPreimage R H := by
    intro n hn
    apply (F.mem_atomicNormalizerPreimage R H n).mpr
    refine ⟨hn.1, ?_⟩
    change F.normalizerToOrbitAut R ⟨n, hn.1⟩ ∈
      F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hRA ≫ f))
    rw [hfg]
    exact F.relativeNormalizer_fixes_restriction hRB g ⟨n, hn⟩
  have hNH : N ≤ F.atomicNormalizerPreimage R H := sup_le hNAH hNBH
  have hw : ∀ n : N, ∃ t : T, ∀ x : R,
      (β.val (R.normalizerMonoidHom ⟨n.val, hNN n.property⟩ x)).val =
        t.val * (β.val x).val * t.val⁻¹ := by
    intro n
    apply F.fixed_normalizer_has_target_witness β ⟨n.val, hNN n.property⟩
    exact ((F.mem_atomicNormalizerPreimage R H n.val).mp (hNH n.property)).choose_spec
  obtain ⟨hh, hallowed, hext⟩ := F.centric_normalizer_extension p sat hRN hNN hR β hw
  let h : (⟨N⟩ : F.Object) ⟶ ⟨T⟩ := ⟨hh, hallowed⟩
  have hraw : F.inclusion hRN ≫ h = β := by
    apply Subtype.ext
    ext x
    exact hext x
  have hres : F.toOrbit.map (F.inclusion hRN ≫ h) =
      F.toOrbit.map (F.inclusion hRA ≫ f) := congrArg F.toOrbit.map hraw
  refine ⟨h, ?_, ?_⟩
  · apply F.centric_orbit_restriction_injective p hS sat hRNA hR
    exact hres
  · apply F.centric_orbit_restriction_injective p hS sat hRNB hR
    exact hres.trans hfg

end Sharpness.FusionSystem
