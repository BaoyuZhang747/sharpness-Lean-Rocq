import Sharpness.CentricKernelTransport
import Sharpness.QuotientLifts

/-! Connecting actual quotient centricity to the automorphism-kernel
argument. Both the subgroup correspondence and conjugate transport are
proved here; neither is a literature-input field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem quotientPreimage_map {P : Subgroup S} (hZP : Z ≤ P) :
    F.quotientPreimage Z (P.map (QuotientGroup.mk' Z)) = P := by
  rw [quotientPreimage, QuotientGroup.comap_map_mk', sup_eq_right.mpr hZP]

theorem subgroupCongr_allowed {P Q : Subgroup S} (h : P = Q) :
    F.IsHom (MulEquiv.subgroupCongr h).toMonoidHom := by
  convert F.inclusion_mem h.le using 1
  apply MonoidHom.ext
  intro x
  rfl

theorem quotient_centric_conjugate_centralizer
    (A : Subgroup (S ⧸ Z)) (hA : I.system.IsCentric A)
    (Q : Subgroup S) (e : F.quotientPreimage Z A ≃* Q)
    (he : F.IsHom e.toMonoidHom) :
    Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z) := by
  have hZQ := (F.central_containment_iff hZ e he).mp (QuotientGroup.le_comap_mk' Z A)
  let B := Q.map (QuotientGroup.mk' Z)
  have eqQ : Q = F.quotientPreimage Z B := (F.quotientPreimage_map hZQ).symm
  let e' := e.trans (MulEquiv.subgroupCongr eqQ)
  have he' : F.IsHom e'.toMonoidHom := F.comp_mem _ _ he (F.subgroupCongr_allowed eqQ)
  let a := @InducedCategory.isoMk (Subgroup (S ⧸ Z)) F.Object inferInstance
    (fun C => (⟨F.quotientPreimage Z C⟩ : F.Object)) A B (F.isoOfMulEquiv e' he')
  let b := (F.quotientRawFunctor hZ p hS sat I).mapIso a
  let eb := I.system.groupEquivOfOrbitIso (I.system.toOrbit.mapIso b)
  have h := hA B le_top eb (I.system.groupEquivOfOrbitIso_allowed _)
  simpa only [inf_top_eq] using h

theorem gamma_inner_of_quotient_centric
    (A : Subgroup (S ⧸ Z)) (hA : I.system.IsCentric A) :
    letI := F.central_subgroupOf_normal hZ (F.quotientPreimage Z A)
    ∀ a : F.Gamma hZ (QuotientGroup.le_comap_mk' Z A),
      ∃ r : F.quotientPreimage Z A, ∀ x, a.val.val x = r⁻¹ * x * r :=
  F.gamma_inner_of_conjugate_centralizers p hS sat hZ
    (F.quotientPreimage Z A) (QuotientGroup.le_comap_mk' Z A)
    (F.quotient_centric_conjugate_centralizer hZ p hS sat I A hA)

end Sharpness.FusionSystem
