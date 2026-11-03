import Sharpness.FullyNormalized
import Sharpness.CentralQuotientDefinition

/-! The inner-kernel argument in Lemma 3.1 at a fully normalized subgroup.
The quotient centralizer is the actual centralizer in the group S/Z. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (P : Subgroup S) (hZP : Z ≤ P) (normalized : F.FullyNormalized P)
    (quotientCentric : Subgroup.centralizer
      (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) ≤ P.map (QuotientGroup.mk' Z))

include hS sat normalized quotientCentric

theorem gamma_inner_fullyNormalized (a : F.Gamma hZ hZP) :
    ∃ r : P, ∀ x : P, a.val.val x = r⁻¹ * x * r := by
  have hp := F.gamma_isPGroup hZ hZP p hS
  have ha := F.normal_p_subgroup_le_conjugation p hS sat P normalized
    (F.Gamma hZ hZP) hp a.property
  obtain ⟨s, hs⟩ := ha
  change P.normalizerMonoidHom s = a.val.val at hs
  have centralizes : (QuotientGroup.mk s.val : S ⧸ Z) ∈
      Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hmod := F.gamma_modZ hZ hZP a ⟨x, hx⟩
    have he : (QuotientGroup.mk x : S ⧸ Z) = QuotientGroup.mk (s.val * x * s.val⁻¹) := by
      apply QuotientGroup.eq.mpr
      change x⁻¹ * (s.val * x * s.val⁻¹) ∈ Z
      have h := congrArg (fun e : MulAut P => (e ⟨x, hx⟩).val) hs
      change s.val * x * s.val⁻¹ = (a.val.val ⟨x, hx⟩).val at h
      rw [h]
      exact hmod
    have conj : (QuotientGroup.mk s.val : S ⧸ Z) * QuotientGroup.mk x *
        (QuotientGroup.mk s.val : S ⧸ Z)⁻¹ = QuotientGroup.mk x := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using he.symm
    calc
      (QuotientGroup.mk' Z) x * QuotientGroup.mk s.val =
          (QuotientGroup.mk s.val * QuotientGroup.mk x *
            (QuotientGroup.mk s.val : S ⧸ Z)⁻¹) * QuotientGroup.mk s.val := by
        rw [conj]
        rfl
      _ = QuotientGroup.mk s.val * (QuotientGroup.mk' Z) x := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
        rfl
  have hsP : s.val ∈ P := by
    have h := quotientCentric centralizes
    have mem : s.val ∈ (P.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) := h
    rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hZP] at mem
    exact mem
  refine ⟨(⟨s.val, hsP⟩ : P)⁻¹, ?_⟩
  intro x
  rw [← hs]
  apply Subtype.ext
  change s.val * x.val * s.val⁻¹ = (s.val⁻¹)⁻¹ * x.val * s.val⁻¹
  rw [inv_inv]

theorem gamma_orbit_trivial_fullyNormalized (a : F.Gamma hZ hZP) :
    F.automorphismToOrbitAut P a.val = 1 := by
  obtain ⟨r, hr⟩ := F.gamma_inner_fullyNormalized p hS sat hZ P hZP normalized quotientCentric a
  apply Iso.ext
  change F.toOrbit.map _ = 𝟙 _
  convert F.inner_orbit_eq_id (⟨P⟩ : F.Object) r using 1
  congr 1
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  exact hr x

end Sharpness.FusionSystem
