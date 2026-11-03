import Sharpness.QuotientSpans
import Sharpness.DoubleCosetTwist

/-! Actual double-coset bijection for two fusion arrows and their induced
quotient arrows, with a projection map that computes on representatives. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)

def projectedDoubleCosetMap : F.RawDoubleCosetTerm f g →
    I.system.RawDoubleCosetTerm (F.projectedFusionHom hZ p hS sat I f)
      (F.projectedFusionHom hZ p hS sat I g) :=
  Quotient.map (F.subgroupProjection Z C) (by
    intro u v h
    obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp h
    obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := hd
    apply DoubleCoset.rel_iff.mpr
    refine ⟨F.quotientInducedHom hZ f (F.subgroupProjection Z A a),
      ⟨F.subgroupProjection Z A a, rfl⟩,
      F.quotientInducedHom hZ g (F.subgroupProjection Z B b),
      ⟨F.subgroupProjection Z B b, rfl⟩, ?_⟩
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply, hv, map_mul, map_mul])

theorem projectedDoubleCosetMap_injective :
    Function.Injective (F.projectedDoubleCosetMap hZ p hS sat I f g) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun u v he => ?_
  apply Quotient.sound
  obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp (Quotient.exact he)
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  obtain ⟨aP, rfl⟩ := F.subgroupProjection_surjective Z A a
  obtain ⟨bP, rfl⟩ := F.subgroupProjection_surjective Z B b
  change F.subgroupProjection Z C v =
    F.quotientInducedHom hZ f (F.subgroupProjection Z A aP) *
      F.subgroupProjection Z C u * F.quotientInducedHom hZ g (F.subgroupProjection Z B bP) at hv
  rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply] at hv
  let z := v * (f.val aP * u * g.val bP)⁻¹
  have hz : z ∈ (F.subgroupProjection Z C).ker := by
    change F.subgroupProjection Z C (v * (f.val aP * u * g.val bP)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hv, mul_inv_cancel]
  apply DoubleCoset.rel_iff.mpr
  refine ⟨z * f.val aP,
    f.val.range.mul_mem (F.subgroupProjection_kernel_le_range hZ f hz) ⟨aP, rfl⟩,
    g.val bP, ⟨bP, rfl⟩, ?_⟩
  dsimp [z]
  group

theorem projectedDoubleCosetMap_surjective :
    Function.Surjective (F.projectedDoubleCosetMap hZ p hS sat I f g) := by
  intro i
  refine Quotient.inductionOn i fun u => ?_
  obtain ⟨uP, rfl⟩ := F.subgroupProjection_surjective Z C u
  exact ⟨DoubleCoset.mk f.val.range g.val.range uP, rfl⟩

def projectedDoubleCosetEquiv : F.RawDoubleCosetTerm f g ≃
    I.system.RawDoubleCosetTerm (F.projectedFusionHom hZ p hS sat I f)
      (F.projectedFusionHom hZ p hS sat I g) :=
  Equiv.ofBijective (F.projectedDoubleCosetMap hZ p hS sat I f g)
    ⟨F.projectedDoubleCosetMap_injective hZ p hS sat I f g,
      F.projectedDoubleCosetMap_surjective hZ p hS sat I f g⟩

end Sharpness.FusionSystem
