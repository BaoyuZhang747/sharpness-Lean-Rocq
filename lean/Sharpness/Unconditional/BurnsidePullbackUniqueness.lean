import Sharpness.Unconditional.BurnsidePullbacks

/-! Uniqueness of the actual centric double-coset pullback decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- Centricity places every centralizer correction inside the actual image
of a fusion morphism. No saturation hypothesis is needed. -/
theorem centric_map_centralizer_mem_range {X T : F.Object}
    (hX : F.IsCentric X.subgroup) (f : X ⟶ T) (z : T.subgroup)
    (hz : ∀ x, z * f.val x = f.val x * z) : z ∈ f.val.range := by
  let L := F.imageSubgroup f
  let j : X.subgroup ≃* L := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective f.val f.property))
  have hj : F.IsHom j.toMonoidHom := (F.toImage f).property
  have hzL : z.val ∈ L := by
    apply (hX L le_top j hj)
    refine ⟨?_, Subgroup.mem_top _⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨x, rfl⟩
    exact congrArg Subtype.val (hz x).symm
  obtain ⟨x, hx⟩ := hzL
  exact ⟨x, Subtype.ext hx⟩

variable {P Q T X : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (u v : T.subgroup) (hX : F.IsCentric X.subgroup)
    (c : X ⟶ F.spanApex f g u) (d : X ⟶ F.spanApex f g v)
    (a : P.subgroup) (b : Q.subgroup)
    (hl : ∀ x, (F.concreteSpan f g v).left.val (d.val x) =
      a⁻¹ * (F.concreteSpan f g u).left.val (c.val x) * a)
    (hr : ∀ x, (F.concreteSpan f g v).right.val (d.val x) =
      b⁻¹ * (F.concreteSpan f g u).right.val (c.val x) * b)

include hX c d a b hl hr

/-- The discrepancy between conjugators for the two legs is absorbed into
the centric source image. -/
theorem span_centralizer_correction_mem_range :
    f.val a * v * (g.val b)⁻¹ * u⁻¹ ∈
      (c ≫ (F.concreteSpan f g u).left ≫ f).val.range := by
  apply F.centric_map_centralizer_mem_range hX
  intro x
  have hd := F.concreteSpan_right_equation f g v (d.val x)
  have hc := F.concreteSpan_right_equation f g u (c.val x)
  change g.val ((F.concreteSpan f g v).right.val (d.val x)) =
    v⁻¹ * f.val ((F.concreteSpan f g v).left.val (d.val x)) * v at hd
  rw [hl x, hr x, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hc] at hd
  have hh := congrArg (fun t : T.subgroup => f.val a * v * t * (g.val b)⁻¹ * u⁻¹) hd
  change (f.val a * v * (g.val b)⁻¹ * u⁻¹) *
    f.val ((F.spanLeft f g u).val (c.val x)) =
    f.val ((F.spanLeft f g u).val (c.val x)) *
      (f.val a * v * (g.val b)⁻¹ * u⁻¹)
  simpa [mul_assoc, concreteSpan] using hh

/-- Two centric incoming factors with the same orbit-category legs have
the same double-coset index. -/
theorem span_doubleCoset_eq_of_legs :
    DoubleCoset.mk f.val.range g.val.range u =
      DoubleCoset.mk f.val.range g.val.range v := by
  obtain ⟨x, hx⟩ := F.span_centralizer_correction_mem_range f g u v hX c d a b hl hr
  apply Quotient.sound
  apply DoubleCoset.rel_iff.mpr
  refine ⟨f.val (a⁻¹ * (F.concreteSpan f g u).left.val (c.val x)),
    ⟨_, rfl⟩, g.val b, ⟨b, rfl⟩, ?_⟩
  change f.val ((F.concreteSpan f g u).left.val (c.val x)) =
    f.val a * v * (g.val b)⁻¹ * u⁻¹ at hx
  rw [map_mul, map_inv, hx]
  group

omit v d hl hr in
/-- The two legs of one concrete span are jointly monic on incoming
centric orbit morphisms. -/
theorem span_orbit_factor_unique
    (d : X ⟶ F.spanApex f g u)
    (hl : ∀ x, (F.concreteSpan f g u).left.val (d.val x) =
      a⁻¹ * (F.concreteSpan f g u).left.val (c.val x) * a)
    (hr : ∀ x, (F.concreteSpan f g u).right.val (d.val x) =
      b⁻¹ * (F.concreteSpan f g u).right.val (c.val x) * b) :
    F.toOrbit.map c = F.toOrbit.map d := by
  obtain ⟨x, hx⟩ := F.span_centralizer_correction_mem_range f g u u hX c d a b hl hr
  have ha : a.val ∈ (F.spanApex f g u).subgroup := by
    apply (F.mem_spanApex_iff f g u a.val).mpr
    refine ⟨a, rfl, (F.concreteSpan f g u).right.val (c.val x) * b, ?_⟩
    rw [map_mul, F.concreteSpan_right_equation]
    change f.val ((F.concreteSpan f g u).left.val (c.val x)) =
      f.val a * u * (g.val b)⁻¹ * u⁻¹ at hx
    change u⁻¹ * f.val ((F.concreteSpan f g u).left.val (c.val x)) * u * g.val b = _
    rw [hx]
    group
  apply (F.orbit_map_eq_iff c d).mpr
  refine ⟨⟨a.val, ha⟩, ?_⟩
  intro y
  apply Subtype.ext
  exact congrArg (fun z : P.subgroup => z.val) (hl y)

omit a b hl hr in
theorem span_doubleCoset_eq_of_orbit_legs
    (hl : F.toOrbit.map (c ≫ (F.concreteSpan f g u).left) =
      F.toOrbit.map (d ≫ (F.concreteSpan f g v).left))
    (hr : F.toOrbit.map (c ≫ (F.concreteSpan f g u).right) =
      F.toOrbit.map (d ≫ (F.concreteSpan f g v).right)) :
    DoubleCoset.mk f.val.range g.val.range u =
      DoubleCoset.mk f.val.range g.val.range v := by
  obtain ⟨a, ha⟩ := (F.orbit_map_eq_iff _ _).mp hl
  obtain ⟨b, hb⟩ := (F.orbit_map_eq_iff _ _).mp hr
  exact F.span_doubleCoset_eq_of_legs f g u v hX c d a b ha hb

omit v d a b hl hr in
theorem span_orbit_factor_unique_of_orbit_legs
    (d : X ⟶ F.spanApex f g u)
    (hl : F.toOrbit.map (c ≫ (F.concreteSpan f g u).left) =
      F.toOrbit.map (d ≫ (F.concreteSpan f g u).left))
    (hr : F.toOrbit.map (c ≫ (F.concreteSpan f g u).right) =
      F.toOrbit.map (d ≫ (F.concreteSpan f g u).right)) :
    F.toOrbit.map c = F.toOrbit.map d := by
  obtain ⟨a, ha⟩ := (F.orbit_map_eq_iff _ _).mp hl
  obtain ⟨b, hb⟩ := (F.orbit_map_eq_iff _ _).mp hr
  exact F.span_orbit_factor_unique f g u hX c a b d ha hb

end Sharpness.FusionSystem
