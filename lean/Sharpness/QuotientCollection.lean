import Sharpness.CentricRadicalQuotient
import Sharpness.QuotientCentricSubgroups
import Sharpness.FusionCentricClosure

/-! The comparison collection X, with its actual closure properties and
centric-radical containment, rather than those properties as assumptions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

def quotientCollection (P : Subgroup S) : Prop :=
  Z ≤ P ∧ I.system.IsCentric (P.map (QuotientGroup.mk' Z))

def quotientIsoOfIso {P Q : Subgroup S} (hZP : Z ≤ P)
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) :
    I.system.toOrbit.obj ⟨P.map (QuotientGroup.mk' Z)⟩ ≅
      I.system.toOrbit.obj ⟨Q.map (QuotientGroup.mk' Z)⟩ := by
  have hZQ := (F.central_containment_iff hZ e he).mp hZP
  let eP := MulEquiv.subgroupCongr (F.quotientPreimage_map hZP)
  let eQ := MulEquiv.subgroupCongr (F.quotientPreimage_map hZQ).symm
  let e' := eP.trans (e.trans eQ)
  have he' : F.IsHom e'.toMonoidHom :=
    F.comp_mem _ _ (F.subgroupCongr_allowed _) (F.comp_mem _ _ he (F.subgroupCongr_allowed _))
  let a := @InducedCategory.isoMk (Subgroup (S ⧸ Z)) F.Object inferInstance
    (fun C => (⟨F.quotientPreimage Z C⟩ : F.Object))
    (P.map (QuotientGroup.mk' Z)) (Q.map (QuotientGroup.mk' Z)) (F.isoOfMulEquiv e' he')
  exact I.system.toOrbit.mapIso ((F.quotientRawFunctor hZ p hS sat I).mapIso a)

theorem quotientCollection_conjugate {P Q : Subgroup S}
    (hP : F.quotientCollection hZ p hS sat I P)
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) :
    F.quotientCollection hZ p hS sat I Q := by
  let a := F.quotientIsoOfIso hZ p hS sat I hP.1 e he
  exact ⟨(F.central_containment_iff hZ e he).mp hP.1,
    I.system.isoSystem.centricIn_of_iso (I.system.groupEquivOfOrbitIso a)
      (I.system.groupEquivOfOrbitIso_allowed a) hP.2⟩

theorem quotientCollection_overgroup {P Q : Subgroup S}
    (hP : F.quotientCollection hZ p hS sat I P) (hPQ : P ≤ Q) :
    F.quotientCollection hZ p hS sat I Q :=
  ⟨hP.1.trans hPQ, I.system.centric_overgroup hP.2 (Subgroup.map_mono hPQ)⟩

theorem quotientCollection_centric {P : Subgroup S}
    (hP : F.quotientCollection hZ p hS sat I P) : F.IsCentric P := by
  have h := F.quotient_centric_preimage hZ p hS sat I _ hP.2
  rw [F.quotientPreimage_map hP.1] at h
  exact h

theorem centric_radical_in_quotientCollection {P : Subgroup S}
    (centric : F.IsCentric P) (radical : F.IsRadical p P) :
    F.quotientCollection hZ p hS sat I P := by
  have hZP := F.central_le_centric hZ centric
  refine ⟨hZP, ?_⟩
  apply F.quotient_centric_of_centric_radical hZ p hS sat I
  · rw [F.quotientPreimage_map hZP]
    exact centric
  · rw [F.quotientPreimage_map hZP]
    exact radical

end Sharpness.FusionSystem
