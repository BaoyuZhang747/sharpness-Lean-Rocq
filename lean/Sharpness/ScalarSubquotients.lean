import Sharpness.MackeyCategory
import Sharpness.MackeySubquotients

/-! Actual kernel and image subfunctors of scalar multiplication, with
the two pointwise short exact sequences used in cor:local. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness.MackeyModule
open CategoryTheory
variable {R : Type u} [CommRing R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B) (r : R)

def scalarEnd (P : C) : M.Value P →ₗ[R] M.Value P := r • LinearMap.id

@[simp] theorem scalarEnd_apply (P : C) (x : M.Value P) : M.scalarEnd r P x = r • x := rfl

def scalarKernel : M.Subfunctor where
  obj P := LinearMap.ker (M.scalarEnd r P)
  pull_closed := by
    intro P Q f x hx
    change r • M.pull f x = 0
    change r • x = 0 at hx
    rw [← map_smul, hx, map_zero]
  push_closed := by
    intro P Q f x hx
    change r • M.push f x = 0
    change r • x = 0 at hx
    rw [← map_smul, hx, map_zero]

def scalarImage : M.Subfunctor where
  obj P := LinearMap.range (M.scalarEnd r P)
  pull_closed := by
    intro P Q f x hx
    obtain ⟨x, rfl⟩ := hx
    exact ⟨M.pull f x, (M.pull f).map_smul r x |>.symm⟩
  push_closed := by
    intro P Q f x hx
    obtain ⟨x, rfl⟩ := hx
    exact ⟨M.push f x, (M.push f).map_smul r x |>.symm⟩

def submoduleInclusion (N : M.Subfunctor) : M.submodule N ⟶ M where
  app P := (N.obj P).subtype
  pull_comm _ _ := rfl
  push_comm _ _ := rfl

def quotientProjection (N : M.Subfunctor) : M ⟶ M.quotient N where
  app P := (N.obj P).mkQ
  pull_comm _ _ := rfl
  push_comm _ _ := rfl

def scalarToImage : M ⟶ M.submodule (M.scalarImage r) where
  app P := (M.scalarEnd r P).rangeRestrict
  pull_comm f x := Subtype.ext ((M.pull f).map_smul r x |>.symm)
  push_comm f x := Subtype.ext ((M.push f).map_smul r x |>.symm)

theorem scalarToImage_surjective (P : C) : Function.Surjective ((M.scalarToImage r).app P) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

theorem scalarKernel_exact (P : C) :
    Function.Exact ((M.submoduleInclusion (M.scalarKernel r)).app P)
      ((M.scalarToImage r).app P) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.property

theorem scalarImage_exact (P : C) :
    Function.Exact ((M.submoduleInclusion (M.scalarImage r)).app P)
      ((M.quotientProjection (M.scalarImage r)).app P) :=
  LinearMap.exact_subtype_mkQ _

theorem scalar_factorization :
    M.scalarToImage r ≫ M.submoduleInclusion (M.scalarImage r) =
      (show M ⟶ M from
        { app P := M.scalarEnd r P
          pull_comm f x := (M.pull f).map_smul r x |>.symm
          push_comm f x := (M.push f).map_smul r x |>.symm }) := rfl

theorem scalarKernel_killed (P : C) (x : (M.submodule (M.scalarKernel r)).Value P) :
    r • x = 0 := Subtype.ext x.property

theorem scalarQuotient_killed (P : C) (x : (M.quotient (M.scalarImage r)).Value P) :
    r • x = 0 := by
  refine Quotient.inductionOn' x fun y => ?_
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

end Sharpness.MackeyModule
