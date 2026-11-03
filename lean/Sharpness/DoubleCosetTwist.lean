import Sharpness.SpanTwist

/-! The actual double-coset bijection induced by changing two orbit-arrow
representatives, together with equality of their Mackey summands. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (r s : T.subgroup)

def rawDoubleCosetTwistMap : F.RawDoubleCosetTerm f g →
    F.RawDoubleCosetTerm (F.twistLeft f r) (F.twistRight g s) :=
  Quotient.map (F.twistedRepresentative r s) (by
    intro u v h
    obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp h
    obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := hd
    apply DoubleCoset.rel_iff.mpr
    refine ⟨(F.twistLeft f r).val a, ⟨a, rfl⟩, (F.twistRight g s).val b, ⟨b, rfl⟩, ?_⟩
    change r⁻¹ * v * s = (r⁻¹ * f.val a * r) * (r⁻¹ * u * s) * (s⁻¹ * g.val b * s)
    rw [hv]
    group)

def rawDoubleCosetUntwistMap :
    F.RawDoubleCosetTerm (F.twistLeft f r) (F.twistRight g s) → F.RawDoubleCosetTerm f g :=
  Quotient.map (fun u => r * u * s⁻¹) (by
    intro u v h
    obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp h
    obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := hd
    apply DoubleCoset.rel_iff.mpr
    refine ⟨f.val a, ⟨a, rfl⟩, g.val b, ⟨b, rfl⟩, ?_⟩
    change v = (r⁻¹ * f.val a * r) * u * (s⁻¹ * g.val b * s) at hv
    change r * v * s⁻¹ = f.val a * (r * u * s⁻¹) * g.val b
    rw [hv]
    group)

def rawDoubleCosetTwistEquiv : F.RawDoubleCosetTerm f g ≃
    F.RawDoubleCosetTerm (F.twistLeft f r) (F.twistRight g s) where
  toFun := F.rawDoubleCosetTwistMap f g r s
  invFun := F.rawDoubleCosetUntwistMap f g r s
  left_inv i := by
    refine Quotient.inductionOn i fun u => ?_
    change DoubleCoset.mk f.val.range g.val.range (r * (r⁻¹ * u * s) * s⁻¹) =
      DoubleCoset.mk f.val.range g.val.range u
    congr 1
    group
  right_inv i := by
    refine Quotient.inductionOn i fun u => ?_
    change DoubleCoset.mk (F.twistLeft f r).val.range (F.twistRight g s).val.range
      (r⁻¹ * (r * u * s⁻¹) * s) = DoubleCoset.mk _ _ u
    congr 1
    group

instance rawDoubleCosetTermFintype [Finite S] : Fintype (F.RawDoubleCosetTerm f g) := by
  unfold RawDoubleCosetTerm DoubleCoset.Quotient
  exact Fintype.ofFinite _

variable [Finite S] {R : Type u} [Ring R]
    (M : MackeyModule.{u,u,w} R F.Orbit F.mackeyShape)

theorem rawDoubleCosetOperator_twist (i : F.RawDoubleCosetTerm f g) :
    F.rawDoubleCosetOperator (F.twistLeft f r) (F.twistRight g s) M
      (F.rawDoubleCosetTwistEquiv f g r s i) = F.rawDoubleCosetOperator f g M i := by
  refine Quotient.inductionOn i fun u => ?_
  exact F.rawSpanOperator_twist f g r s M u

end Sharpness.FusionSystem
