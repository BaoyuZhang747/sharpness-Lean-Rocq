import Sharpness.SpanOperator
import Sharpness.SubgroupEqualityIso

/-! Changing the two fusion homomorphism representatives by independent
target inner automorphisms preserves the actual span operator. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (r s : T.subgroup)

abbrev twistLeft := f ≫ F.inner T r
abbrev twistRight := g ≫ F.inner T s
def twistedRepresentative (u : T.subgroup) : T.subgroup := r⁻¹ * u * s

theorem twisted_span_equation_iff (u : T.subgroup) (x : P.subgroup) (y : Q.subgroup) :
    (F.twistRight g s).val y = (F.twistedRepresentative r s u)⁻¹ *
      (F.twistLeft f r).val x * F.twistedRepresentative r s u ↔
        g.val y = u⁻¹ * f.val x * u := by
  change s⁻¹ * g.val y * s =
    (r⁻¹ * u * s)⁻¹ * (r⁻¹ * f.val x * r) * (r⁻¹ * u * s) ↔ _
  have h : (r⁻¹ * u * s)⁻¹ * (r⁻¹ * f.val x * r) * (r⁻¹ * u * s) =
      s⁻¹ * (u⁻¹ * f.val x * u) * s := by group
  rw [h]
  constructor
  · intro he
    exact mul_left_cancel (mul_right_cancel he)
  · intro he
    rw [he]

theorem span_twist_subgroup_eq (u : T.subgroup) :
    (F.spanApex (F.twistLeft f r) (F.twistRight g s)
      (F.twistedRepresentative r s u)).subgroup = (F.spanApex f g u).subgroup := by
  ext x
  rw [F.mem_spanApex_iff, F.mem_spanApex_iff]
  constructor
  · rintro ⟨xP, hx, y, hy⟩
    exact ⟨xP, hx, y, (F.twisted_span_equation_iff f g r s u xP y).mp hy⟩
  · rintro ⟨xP, hx, y, hy⟩
    exact ⟨xP, hx, y, (F.twisted_span_equation_iff f g r s u xP y).mpr hy⟩

def spanTwistIso (u : T.subgroup) :
    F.spanApex (F.twistLeft f r) (F.twistRight g s) (F.twistedRepresentative r s u) ≅
      F.spanApex f g u := F.subgroupEqualityIso (F.span_twist_subgroup_eq f g r s u)

theorem spanTwist_left_square (u : T.subgroup) :
    F.spanLeft (F.twistLeft f r) (F.twistRight g s) (F.twistedRepresentative r s u) =
      (F.spanTwistIso f g r s u).hom ≫ F.spanLeft f g u := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  rfl

theorem spanTwist_right_square (u : T.subgroup) :
    (F.concreteSpan (F.twistLeft f r) (F.twistRight g s) (F.twistedRepresentative r s u)).right =
      (F.spanTwistIso f g r s u).hom ≫ (F.concreteSpan f g u).right := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply F.injective g.val g.property
  have hn := F.concreteSpan_right_equation (F.twistLeft f r) (F.twistRight g s)
    (F.twistedRepresentative r s u) x
  have hb := (F.twisted_span_equation_iff f g r s u _ _).mp hn
  have ho := F.concreteSpan_right_equation f g u ((F.spanTwistIso f g r s u).hom.val x)
  exact hb.trans ho.symm

variable [Finite S] {R : Type u} [Ring R]
    (M : MackeyModule.{u,u,w} R F.Orbit F.mackeyShape)

theorem rawSpanOperator_twist (u : T.subgroup) :
    F.rawSpanOperator (F.twistLeft f r) (F.twistRight g s) M (F.twistedRepresentative r s u) =
      F.rawSpanOperator f g M u := by
  apply M.span_operator_of_iso
    (F.concreteOrbitSpan (F.twistLeft f r) (F.twistRight g s) (F.twistedRepresentative r s u))
    (F.concreteOrbitSpan f g u) (F.toOrbit.mapIso (F.spanTwistIso f g r s u))
  · exact (congrArg (fun t => F.toOrbit.map t) (F.spanTwist_left_square f g r s u)).trans
      (F.toOrbit.map_comp _ _)
  · exact (congrArg (fun t => F.toOrbit.map t) (F.spanTwist_right_square f g r s u)).trans
      (F.toOrbit.map_comp _ _)

end Sharpness.FusionSystem
