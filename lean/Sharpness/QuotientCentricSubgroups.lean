import Sharpness.QuotientCentric

/-! The actual preimage of a quotient-centric subgroup is F-centric. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem quotient_centric_preimage (A : Subgroup (S ⧸ Z)) (hA : I.system.IsCentric A) :
    F.IsCentric (F.quotientPreimage Z A) := by
  intro Q _ e he x hx
  have hZQ := (F.central_containment_iff hZ e he).mp (QuotientGroup.le_comap_mk' Z A)
  have hc : (QuotientGroup.mk' Z) x ∈ Subgroup.centralizer
      (Q.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hq
    have h := (Subgroup.mem_centralizer_iff.mp hx.1) y hy
    simpa only [map_mul] using congrArg (QuotientGroup.mk' Z) h
  have hm := F.quotient_centric_conjugate_centralizer hZ p hS sat I A hA Q e he hc
  change x ∈ F.quotientPreimage Z (Q.map (QuotientGroup.mk' Z)) at hm
  rw [F.quotientPreimage_map hZQ] at hm
  exact hm

end Sharpness.FusionSystem
