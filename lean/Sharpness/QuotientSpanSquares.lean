import Sharpness.QuotientSpans
import Sharpness.QuotientLifts

/-! The left and right arrows of the actual quotient span are induced by
the original arrows, after the proved preimage identification. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem rawQuotientOrbitMap_projected {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    F.rawQuotientOrbitMap hZ p hS sat I f =
      I.system.toOrbit.map (F.projectedFusionHom hZ p hS sat I f) := rfl

variable {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (u : F.quotientPreimage Z C)

def spanQuotientLeft :
    (⟨F.quotientPreimage Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup⟩ : F.Object) ⟶
      ⟨F.quotientPreimage Z A⟩ :=
  (F.spanQuotientPreimageIso hZ p hS sat I f g u).inv ≫ F.spanLeft f g u

def spanQuotientRight :
    (⟨F.quotientPreimage Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup⟩ : F.Object) ⟶
      ⟨F.quotientPreimage Z B⟩ :=
  (F.spanQuotientPreimageIso hZ p hS sat I f g u).inv ≫ (F.concreteSpan f g u).right

theorem projected_spanQuotientLeft :
    F.projectedFusionHom hZ p hS sat I (F.spanQuotientLeft hZ p hS sat I f g u) =
      I.system.spanLeft (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z
    (F.projectedSpanApex hZ p hS sat I f g u).subgroup a
  rw [F.quotientInducedHom_apply]
  apply Subtype.ext
  rfl

theorem projected_spanQuotientRight :
    F.projectedFusionHom hZ p hS sat I (F.spanQuotientRight hZ p hS sat I f g u) =
      (I.system.concreteSpan (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)).right := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z
    (F.projectedSpanApex hZ p hS sat I f g u).subgroup a
  rw [F.quotientInducedHom_apply]
  apply I.system.injective (F.projectedFusionHom hZ p hS sat I g).val
    (F.projectedFusionHom hZ p hS sat I g).property
  let xOld := (F.spanQuotientPreimageIso hZ p hS sat I f g u).inv.val x
  have hx : (I.system.spanLeft (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)).val
      (F.subgroupProjection Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup x) =
      F.subgroupProjection Z A ((F.spanLeft f g u).val xOld) := by
    apply Subtype.ext
    rfl
  have hf := (congrArg (F.quotientInducedHom hZ f) hx).trans
    (F.quotientInducedHom_apply hZ f ((F.spanLeft f g u).val xOld))
  have hp : F.subgroupProjection Z C (g.val ((F.concreteSpan f g u).right.val xOld)) =
      (F.subgroupProjection Z C u)⁻¹ *
        F.subgroupProjection Z C (f.val ((F.spanLeft f g u).val xOld)) * F.subgroupProjection Z C u := by
    simpa only [map_mul, map_inv] using
      congrArg (F.subgroupProjection Z C) (F.concreteSpan_right_equation f g u xOld)
  have hm := congrArg (fun t => (F.subgroupProjection Z C u)⁻¹ * t * F.subgroupProjection Z C u) hf.symm
  have hb := I.system.concreteSpan_right_equation (F.projectedFusionHom hZ p hS sat I f)
    (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)
    (F.subgroupProjection Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup x)
  exact (F.quotientInducedHom_apply hZ g ((F.spanQuotientRight hZ p hS sat I f g u).val x)).trans
    (hp.trans (hm.trans hb.symm))

end Sharpness.FusionSystem
