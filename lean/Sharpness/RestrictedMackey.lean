import Sharpness.HigherLimits
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Restricted Mackey functors with the centric-truncated formula of DP 2.1.
The passage from a supported full Mackey functor to this definition is
proved by removing exactly the zero noncentric summands.
-/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory
open scoped BigOperators

variable {C : Type v} [Category.{v} C] (B : MackeyShape C) (K : ObjectProperty C)

abbrev RestrictedTerm {P Q T : K.FullSubcategory} (f : P ⟶ T) (g : Q ⟶ T) :=
  {i : B.Term f.hom g.hom // K (B.span f.hom g.hom i).apex}

instance restrictedTermFintype {P Q T : K.FullSubcategory} (f : P ⟶ T) (g : Q ⟶ T) :
    Fintype (RestrictedTerm B K f g) := by
  classical
  infer_instance

def restrictedSpan {P Q T : K.FullSubcategory} (f : P ⟶ T) (g : Q ⟶ T)
    (i : RestrictedTerm B K f g) : MackeySpan K.FullSubcategory P Q where
  apex := ⟨(B.span f.hom g.hom i.val).apex, i.property⟩
  left := ⟨(B.span f.hom g.hom i.val).left⟩
  right := ⟨(B.span f.hom g.hom i.val).right⟩

structure RestrictedMackeyModule (R : Type u) [Ring R] (C : Type v) [Category.{v} C]
    (B : MackeyShape C) (K : ObjectProperty C) where
  Value : K.FullSubcategory → Type w
  valueAddCommGroup : ∀ P, AddCommGroup (Value P)
  valueModule : ∀ P, Module R (Value P)
  pull : ∀ {P Q : K.FullSubcategory}, (P ⟶ Q) → Value Q →ₗ[R] Value P
  push : ∀ {P Q : K.FullSubcategory}, (P ⟶ Q) → Value P →ₗ[R] Value Q
  pull_id : ∀ P, pull (𝟙 P) = LinearMap.id
  push_id : ∀ P, push (𝟙 P) = LinearMap.id
  pull_comp : ∀ {P Q T : K.FullSubcategory} (f : P ⟶ Q) (g : Q ⟶ T),
    pull (f ≫ g) = (pull f).comp (pull g)
  push_comp : ∀ {P Q T : K.FullSubcategory} (f : P ⟶ Q) (g : Q ⟶ T),
    push (f ≫ g) = (push g).comp (push f)
  pull_iso : ∀ {P Q : K.FullSubcategory} (f : P ⟶ Q) [IsIso f], pull f = push (inv f)
  mackey : ∀ {P Q T : K.FullSubcategory} (f : P ⟶ T) (g : Q ⟶ T),
    (pull f).comp (push g) = ∑ i : RestrictedTerm B K f g,
      (push (restrictedSpan B K f g i).left).comp (pull (restrictedSpan B K f g i).right)

attribute [instance] RestrictedMackeyModule.valueAddCommGroup RestrictedMackeyModule.valueModule

namespace RestrictedMackeyModule
variable {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    {B : MackeyShape C} {K : ObjectProperty C} (M : RestrictedMackeyModule.{u,u,u} R C B K)

def coefficient : CoefficientCategory R K.FullSubcategory where
  obj P := ModuleCat.of R (M.Value P.unop)
  map f := ModuleCat.ofHom (M.pull f.unop)
  map_id P := by apply ModuleCat.hom_ext; exact M.pull_id P.unop
  map_comp f g := by apply ModuleCat.hom_ext; exact M.pull_comp g.unop f.unop

end RestrictedMackeyModule

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B) (K : ObjectProperty C)
    (supported : ∀ P, ¬ K P → ∀ x : M.Value P, x = 0)

include supported

theorem summand_zero_off {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T)
    (i : B.Term f g) (hi : ¬ K (B.span f g i).apex) :
    (M.push (B.span f g i).left).comp (M.pull (B.span f g i).right) = 0 := by
  apply LinearMap.ext
  intro x
  change M.push (B.span f g i).left (M.pull (B.span f g i).right x) = 0
  rw [supported _ hi (M.pull (B.span f g i).right x), map_zero]

def restrictSupported : RestrictedMackeyModule R C B K where
  Value P := M.Value P.obj
  valueAddCommGroup P := M.valueAddCommGroup P.obj
  valueModule P := M.valueModule P.obj
  pull f := M.pull f.hom
  push f := M.push f.hom
  pull_id P := M.pull_id P.obj
  push_id P := M.push_id P.obj
  pull_comp f g := M.pull_comp f.hom g.hom
  push_comp f g := M.push_comp f.hom g.hom
  pull_iso f := by
    intro hf
    letI : IsIso f.hom := ((ObjectProperty.ι K).mapIso (asIso f)).isIso_hom
    have h := M.pull_iso f.hom
    simpa using h
  mackey f g := by
    classical
    rw [M.mackey]
    symm
    let op := fun i : B.Term f.hom g.hom =>
      (M.push (B.span f.hom g.hom i).left).comp (M.pull (B.span f.hom g.hom i).right)
    change (∑ i : RestrictedTerm B K f g, op i.val) = ∑ i, op i
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => K (B.span f.hom g.hom i).apex), op i :=
        (Finset.sum_subtype _ (by simp) op).symm
      _ = _ := Finset.sum_subset (Finset.filter_subset _ _) (by
        intro i _ hi
        have hn : ¬ K (B.span f.hom g.hom i).apex := by simpa using hi
        exact M.summand_zero_off K supported f.hom g.hom i hn)

end MackeyModule
end Sharpness
