import Sharpness.SpanShift

/-! Independence of the actual Mackey summand from its double-coset
representative, proved using the concrete conjugation apex isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)

def concreteOrbitSpan (u : T.subgroup) :
    MackeySpan F.Orbit (F.toOrbit.obj P) (F.toOrbit.obj Q) where
  apex := F.toOrbit.obj (F.spanApex f g u)
  left := F.toOrbit.map (F.spanLeft f g u)
  right := F.toOrbit.map (F.concreteSpan f g u).right

theorem orbit_map_post_inner {A B : F.Object} (h : A ⟶ B) (r : B.subgroup) :
    F.toOrbit.map (h ≫ F.inner B r) = F.toOrbit.map h :=
  (F.toOrbit.map_comp _ _).trans
    ((congrArg (fun t => F.toOrbit.map h ≫ t) (F.inner_orbit_eq_id B r)).trans
      (Category.comp_id (F.toOrbit.map h)))

theorem spanShift_orbit_left (u : T.subgroup) (a : P.subgroup) (b : Q.subgroup) :
    (F.concreteOrbitSpan f g u).left =
      (F.toOrbit.mapIso (F.spanShiftIso f g u a b)).hom ≫
        (F.concreteOrbitSpan f g (F.shiftedRepresentative f g u a b)).left := by
  change F.toOrbit.map (F.spanLeft f g u) =
    F.toOrbit.map (F.spanShiftIso f g u a b).hom ≫
      F.toOrbit.map (F.spanLeft f g (F.shiftedRepresentative f g u a b))
  exact (F.orbit_map_post_inner _ _).symm.trans
    ((congrArg (fun t => F.toOrbit.map t) (F.spanShift_left_square f g u a b)).trans
      (F.toOrbit.map_comp _ _))

theorem spanShift_orbit_right (u : T.subgroup) (a : P.subgroup) (b : Q.subgroup) :
    (F.concreteOrbitSpan f g u).right =
      (F.toOrbit.mapIso (F.spanShiftIso f g u a b)).hom ≫
        (F.concreteOrbitSpan f g (F.shiftedRepresentative f g u a b)).right := by
  change F.toOrbit.map (F.concreteSpan f g u).right =
    F.toOrbit.map (F.spanShiftIso f g u a b).hom ≫
      F.toOrbit.map (F.concreteSpan f g (F.shiftedRepresentative f g u a b)).right
  exact (F.orbit_map_post_inner _ _).symm.trans
    ((congrArg (fun t => F.toOrbit.map t) (F.spanShift_right_square f g u a b)).trans
      (F.toOrbit.map_comp _ _))

abbrev RawDoubleCosetTerm := DoubleCoset.Quotient (f.val.range : Set T.subgroup) g.val.range

variable [Finite S] {R : Type u} [Ring R]
    (M : MackeyModule.{u,u,w} R F.Orbit F.mackeyShape)

def rawSpanOperator (u : T.subgroup) :
    M.Value (F.toOrbit.obj Q) →ₗ[R] M.Value (F.toOrbit.obj P) :=
  (M.push (F.concreteOrbitSpan f g u).left).comp (M.pull (F.concreteOrbitSpan f g u).right)

theorem rawSpanOperator_shift (u : T.subgroup) (a : P.subgroup) (b : Q.subgroup) :
    F.rawSpanOperator f g M u =
      F.rawSpanOperator f g M (F.shiftedRepresentative f g u a b) :=
  M.span_operator_of_iso (F.concreteOrbitSpan f g u)
    (F.concreteOrbitSpan f g (F.shiftedRepresentative f g u a b))
    (F.toOrbit.mapIso (F.spanShiftIso f g u a b))
    (F.spanShift_orbit_left f g u a b) (F.spanShift_orbit_right f g u a b)

theorem rawSpanOperator_eq_of_doubleCoset_eq (u v : T.subgroup)
    (same : DoubleCoset.mk f.val.range g.val.range u =
      DoubleCoset.mk f.val.range g.val.range v) :
    F.rawSpanOperator f g M u = F.rawSpanOperator f g M v := by
  obtain ⟨c, hc, d, hd, h⟩ := DoubleCoset.rel_iff.mp (Quotient.exact same)
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  rw [h]
  exact F.rawSpanOperator_shift f g M u a b

def rawDoubleCosetOperator (i : F.RawDoubleCosetTerm f g) :
    M.Value (F.toOrbit.obj Q) →ₗ[R] M.Value (F.toOrbit.obj P) :=
  Quotient.lift (F.rawSpanOperator f g M)
    (fun u v h => F.rawSpanOperator_eq_of_doubleCoset_eq f g M u v (Quotient.sound h)) i

theorem rawDoubleCosetOperator_out (i : F.RawDoubleCosetTerm f g) :
    F.rawDoubleCosetOperator f g M i = F.rawSpanOperator f g M i.out := by
  exact (congrArg (fun j => F.rawDoubleCosetOperator f g M j) (Quotient.out_eq i)).symm

end Sharpness.FusionSystem
