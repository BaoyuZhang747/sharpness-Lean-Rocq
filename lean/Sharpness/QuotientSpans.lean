import Sharpness.QuotientImage
import Sharpness.QuotientOrbit
import Sharpness.SpanEquations
import Sharpness.SubgroupEqualityIso

/-! The actual intersection span in the quotient has precisely the
original span as its full preimage. The converse uses exact image lifting,
not a cardinality assumption or an assumed span correspondence. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

abbrev projectedFusionHom {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    (⟨A⟩ : I.system.Object) ⟶ ⟨B⟩ :=
  ⟨F.quotientInducedHom hZ f, (I.isHom_iff _).mpr ⟨f, rfl⟩⟩

variable {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (u : F.quotientPreimage Z C)

abbrev projectedSpanApex : I.system.Object :=
  I.system.spanApex (F.projectedFusionHom hZ p hS sat I f)
    (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)

theorem spanApex_quotient_preimage : (F.spanApex f g u).subgroup =
    F.quotientPreimage Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup := by
  ext x
  change x ∈ (F.spanApex f g u).subgroup ↔
    QuotientGroup.mk x ∈ (F.projectedSpanApex hZ p hS sat I f g u).subgroup
  constructor
  · intro hx
    obtain ⟨xP, hxP, y, hy⟩ := (F.mem_spanApex_iff f g u x).mp hx
    apply (I.system.mem_spanApex_iff _ _ _ _).mpr
    refine ⟨F.subgroupProjection Z A xP, congrArg (QuotientGroup.mk' Z) hxP,
      F.subgroupProjection Z B y, ?_⟩
    change F.quotientInducedHom hZ g (F.subgroupProjection Z B y) =
      (F.subgroupProjection Z C u)⁻¹ *
        F.quotientInducedHom hZ f (F.subgroupProjection Z A xP) * F.subgroupProjection Z C u
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply, hy,
      map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨xA, hxA, yB, hyB⟩ := (I.system.mem_spanApex_iff _ _ _ _).mp hx
    change xA.val = (QuotientGroup.mk' Z) x at hxA
    have hxP : x ∈ F.quotientPreimage Z A := by
      change (QuotientGroup.mk' Z) x ∈ A
      rw [← hxA]
      exact xA.property
    let xP : F.quotientPreimage Z A := ⟨x, hxP⟩
    have hπx : F.subgroupProjection Z A xP = xA := Subtype.ext hxA.symm
    let w : F.quotientPreimage Z C := u⁻¹ * f.val xP * u
    have himage : F.subgroupProjection Z C w ∈ (F.quotientInducedHom hZ g).range := by
      refine ⟨yB, ?_⟩
      change F.quotientInducedHom hZ g yB =
        (F.subgroupProjection Z C u)⁻¹ * F.quotientInducedHom hZ f xA *
          F.subgroupProjection Z C u at hyB
      rw [← hπx, F.quotientInducedHom_apply] at hyB
      simpa only [w, map_mul, map_inv] using hyB
    obtain ⟨y, hy⟩ := (F.quotient_image_iff hZ g w).mp himage
    exact (F.mem_spanApex_iff f g u x).mpr ⟨xP, rfl, y, hy⟩

def spanQuotientPreimageIso : F.spanApex f g u ≅
    (⟨F.quotientPreimage Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup⟩ : F.Object) :=
  F.subgroupEqualityIso (F.spanApex_quotient_preimage hZ p hS sat I f g u)

end Sharpness.FusionSystem
