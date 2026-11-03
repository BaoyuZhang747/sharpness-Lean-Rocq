import Sharpness.QuotientBadCentralizer
import Sharpness.QuotientIsoLaw
import Sharpness.Radical

/-! Centric-radical preimages have centric images in the actual central
quotient. This proves the centric-radical inclusion required before the
Yalcin 10.5 comparison can be invoked. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem quotientPreimage_image (A : Subgroup (S ⧸ Z)) :
    (F.quotientPreimage Z A).map (QuotientGroup.mk' Z) = A := by
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hq
    obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨s, (show (QuotientGroup.mk' Z) s ∈ A from hs.symm ▸ hq), hs⟩

include hS hZ

theorem quotient_centralizer_le_of_radical (P : Subgroup S) (hZP : Z ≤ P)
    (centric : F.IsCentric P) (radical : F.IsRadical p P) :
    Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) ≤
      P.map (QuotientGroup.mk' Z) := by
  classical
  by_contra bad
  letI := F.central_subgroupOf_normal hZ P
  have hn := F.orbitGamma_nontrivial_of_bad_quotient_centralizer hZ P hZP centric bad
  exact hn (radical (F.orbitGamma hZ hZP) (F.orbitGamma_normal hZ hZP)
    (F.orbitGamma_isPGroup hZ hZP p hS))

theorem quotient_centric_of_centric_radical (A : Subgroup (S ⧸ Z))
    (centric : F.IsCentric (F.quotientPreimage Z A))
    (radical : F.IsRadical p (F.quotientPreimage Z A)) : I.system.IsCentric A := by
  intro B _ e he x hx
  let a := I.system.toOrbit.mapIso (I.system.isoOfMulEquiv e he)
  let l := F.quotientOrbitLiftIso hZ p hS sat I a.hom
  let lO := F.toOrbit.mapIso l
  have hc : F.IsCentric (F.quotientPreimage Z B) :=
    F.isoSystem.centricIn_of_iso (F.groupEquivOfOrbitIso lO)
      (F.groupEquivOfOrbitIso_allowed lO) centric
  have hr : F.IsRadical p (F.quotientPreimage Z B) := F.radical_of_orbitIso lO radical
  have h := F.quotient_centralizer_le_of_radical hZ p hS
    (F.quotientPreimage Z B) (QuotientGroup.le_comap_mk' Z B) hc hr
  rw [F.quotientPreimage_image B] at h
  exact h hx.1

end Sharpness.FusionSystem
