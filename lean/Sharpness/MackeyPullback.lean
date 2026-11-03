import Sharpness.MackeySubquotients

/-!
Pulling full Mackey coefficients through a functor that identifies the
complete double-coset span decompositions. This supplies the Mackey-formula
part of restriction and quotient inflation without assuming an acyclicity
or descent theorem.
-/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory
open scoped BigOperators

structure MackeyMap {C D : Type v} [Category.{v} C] [Category.{v} D]
    (B : MackeyShape C) (B' : MackeyShape D) where
  functor : C ⥤ D
  terms : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T),
    B.Term f g ≃ B'.Term (functor.map f) (functor.map g)
  apexIso : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T) (i : B.Term f g),
    functor.obj (B.span f g i).apex ≅
      (B'.span (functor.map f) (functor.map g) (terms f g i)).apex
  left_comm : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T) (i : B.Term f g),
    functor.map (B.span f g i).left = (apexIso f g i).hom ≫
      (B'.span (functor.map f) (functor.map g) (terms f g i)).left
  right_comm : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T) (i : B.Term f g),
    functor.map (B.span f g i).right = (apexIso f g i).hom ≫
      (B'.span (functor.map f) (functor.map g) (terms f g i)).right

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B)

theorem push_pull_iso {P Q : C} (e : P ≅ Q) :
    (M.push e.hom).comp (M.pull e.hom) = LinearMap.id := by
  have hi : M.pull e.hom = M.push e.inv := by simpa using M.pull_iso e.hom
  rw [hi, ← M.push_comp, e.inv_hom_id, M.push_id]

end MackeyModule

namespace MackeyMap
variable {R : Type u} [Ring R] {C D : Type v} [Category.{v} C] [Category.{v} D]
    {B : MackeyShape C} {B' : MackeyShape D}
    (F : MackeyMap B B') (M : MackeyModule.{u,v,w} R D B')

theorem span_operator {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T) (i : B.Term f g) :
    (M.push (F.functor.map (B.span f g i).left)).comp
      (M.pull (F.functor.map (B.span f g i).right)) =
    (M.push (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).left).comp
      (M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right) := by
  rw [F.left_comm, F.right_comm, M.push_comp, M.pull_comp]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  have hi := LinearMap.congr_fun (M.push_pull_iso (F.apexIso f g i))
    (M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right x)
  change M.push (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).left
    (M.push (F.apexIso f g i).hom
      (M.pull (F.apexIso f g i).hom
        (M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right x))) = _
  rw [show M.push (F.apexIso f g i).hom
      (M.pull (F.apexIso f g i).hom
        (M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right x)) =
      M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right x from hi]

def pullback : MackeyModule R C B where
  Value P := M.Value (F.functor.obj P)
  valueAddCommGroup P := M.valueAddCommGroup (F.functor.obj P)
  valueModule P := M.valueModule (F.functor.obj P)
  pull f := M.pull (F.functor.map f)
  push f := M.push (F.functor.map f)
  pull_id P := by rw [F.functor.map_id, M.pull_id]
  push_id P := by rw [F.functor.map_id, M.push_id]
  pull_comp f g := by rw [F.functor.map_comp, M.pull_comp]
  push_comp f g := by rw [F.functor.map_comp, M.push_comp]
  pull_iso f := by
    intro hf
    letI : IsIso (F.functor.map f) := (F.functor.mapIso (asIso f)).isIso_hom
    have h := M.pull_iso (F.functor.map f)
    simpa only [F.functor.map_inv] using h
  mackey f g := by
    rw [M.mackey]
    symm
    calc
      _ = ∑ i : B.Term f g,
          (M.push (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).left).comp
            (M.pull (B'.span (F.functor.map f) (F.functor.map g) (F.terms f g i)).right) :=
        Finset.sum_congr rfl (fun i _ => F.span_operator M f g i)
      _ = _ := (F.terms f g).sum_comp
        (fun i : B'.Term (F.functor.map f) (F.functor.map g) =>
          (M.push (B'.span (F.functor.map f) (F.functor.map g) i).left).comp
            (M.pull (B'.span (F.functor.map f) (F.functor.map g) i).right))

end MackeyMap
end Sharpness
