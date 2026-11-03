import Sharpness.DoubleCosetTwist

/-! The two functor structures before a Mackey identity is proved. This
intermediate type deliberately has no Mackey formula field: the formula
must be supplied by a proved theorem before `toMackey` can be constructed. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness
open CategoryTheory
open scoped BigOperators

structure MackeyFunctorData (R : Type u) [Ring R] (C : Type u) [Category.{u} C] where
  Value : C → Type w
  valueAddCommGroup : ∀ P, AddCommGroup (Value P)
  valueModule : ∀ P, Module R (Value P)
  pull : ∀ {P Q}, (P ⟶ Q) → Value Q →ₗ[R] Value P
  push : ∀ {P Q}, (P ⟶ Q) → Value P →ₗ[R] Value Q
  pull_id : ∀ P, pull (𝟙 P) = LinearMap.id
  push_id : ∀ P, push (𝟙 P) = LinearMap.id
  pull_comp : ∀ {P Q T} (f : P ⟶ Q) (g : Q ⟶ T), pull (f ≫ g) = (pull f).comp (pull g)
  push_comp : ∀ {P Q T} (f : P ⟶ Q) (g : Q ⟶ T), push (f ≫ g) = (push g).comp (push f)
  pull_iso : ∀ {P Q} (f : P ⟶ Q) [IsIso f], pull f = push (inv f)

attribute [instance] MackeyFunctorData.valueAddCommGroup MackeyFunctorData.valueModule

namespace MackeyFunctorData
variable {R : Type u} [Ring R] {C : Type u} [Category.{u} C] (E : MackeyFunctorData.{u,w} R C)

theorem push_pull_iso {P Q : C} (e : P ≅ Q) :
    (E.push e.hom).comp (E.pull e.hom) = LinearMap.id := by
  have hi : E.pull e.hom = E.push e.inv := by simpa using E.pull_iso e.hom
  rw [hi, ← E.push_comp, e.inv_hom_id, E.push_id]

def spanOperator {P Q : C} (s : MackeySpan C P Q) := (E.push s.left).comp (E.pull s.right)

theorem spanOperator_of_iso {P Q : C} (s t : MackeySpan C P Q)
    (e : s.apex ≅ t.apex) (hl : s.left = e.hom ≫ t.left)
    (hr : s.right = e.hom ≫ t.right) : E.spanOperator s = E.spanOperator t := by
  rw [spanOperator, spanOperator, hl, hr, E.push_comp, E.pull_comp]
  apply LinearMap.ext
  intro x
  change E.push t.left (E.push e.hom (E.pull e.hom (E.pull t.right x))) = _
  have h := LinearMap.congr_fun (E.push_pull_iso e) (E.pull t.right x)
  change E.push e.hom (E.pull e.hom (E.pull t.right x)) = E.pull t.right x at h
  rw [h]
  rfl

def toMackey (B : MackeyShape C)
    (identity : ∀ {P Q T} (f : P ⟶ T) (g : Q ⟶ T),
      (E.pull f).comp (E.push g) = ∑ i : B.Term f g, E.spanOperator (B.span f g i)) :
    MackeyModule R C B where
  Value := E.Value
  valueAddCommGroup := E.valueAddCommGroup
  valueModule := E.valueModule
  pull := E.pull
  push := E.push
  pull_id := E.pull_id
  push_id := E.push_id
  pull_comp := E.pull_comp
  push_comp := E.push_comp
  pull_iso := E.pull_iso
  mackey := identity

end MackeyFunctorData

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [Ring R] (E : MackeyFunctorData.{u,w} R F.Orbit)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)

def functorDataSpanOperator (u : T.subgroup) := E.spanOperator (F.concreteOrbitSpan f g u)

theorem functorDataSpanOperator_shift (u : T.subgroup) (a : P.subgroup) (b : Q.subgroup) :
    F.functorDataSpanOperator E f g u =
      F.functorDataSpanOperator E f g (F.shiftedRepresentative f g u a b) :=
  E.spanOperator_of_iso (F.concreteOrbitSpan f g u)
    (F.concreteOrbitSpan f g (F.shiftedRepresentative f g u a b))
    (F.toOrbit.mapIso (F.spanShiftIso f g u a b))
    (F.spanShift_orbit_left f g u a b) (F.spanShift_orbit_right f g u a b)

theorem functorDataSpanOperator_eq_of_doubleCoset_eq (u v : T.subgroup)
    (same : DoubleCoset.mk f.val.range g.val.range u = DoubleCoset.mk f.val.range g.val.range v) :
    F.functorDataSpanOperator E f g u = F.functorDataSpanOperator E f g v := by
  obtain ⟨c, hc, d, hd, h⟩ := DoubleCoset.rel_iff.mp (Quotient.exact same)
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  rw [h]
  exact F.functorDataSpanOperator_shift E f g u a b

def functorDataDoubleCosetOperator (i : F.RawDoubleCosetTerm f g) :
    E.Value (F.toOrbit.obj Q) →ₗ[R] E.Value (F.toOrbit.obj P) :=
  Quotient.lift (F.functorDataSpanOperator E f g)
    (fun u v h => F.functorDataSpanOperator_eq_of_doubleCoset_eq E f g u v (Quotient.sound h)) i

theorem functorDataDoubleCosetOperator_out (i : F.RawDoubleCosetTerm f g) :
    F.functorDataDoubleCosetOperator E f g i = F.functorDataSpanOperator E f g i.out :=
  (congrArg (fun j => F.functorDataDoubleCosetOperator E f g j) (Quotient.out_eq i)).symm

def fullMackeyOfRawIdentity
    (identity : ∀ {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T),
      (E.pull (F.toOrbit.map f)).comp (E.push (F.toOrbit.map g)) =
        ∑ i : F.RawDoubleCosetTerm f g, F.functorDataDoubleCosetOperator E f g i) :
    MackeyModule R F.Orbit F.mackeyShape :=
  E.toMackey F.mackeyShape (by
    intro P Q T f g
    have h := identity (F.orbitRepresentative f) (F.orbitRepresentative g)
    rw [F.orbitRepresentative_map, F.orbitRepresentative_map] at h
    exact h.trans (Finset.sum_congr rfl (fun i _ =>
      F.functorDataDoubleCosetOperator_out E _ _ i)))

end FusionSystem
end Sharpness
