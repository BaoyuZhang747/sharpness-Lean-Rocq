import Sharpness.Mackey

/-! The actual category of full Mackey modules. Morphisms are linear
families commuting with both restrictions and transfers, so a category
isomorphism expresses the manuscript's full Mackey isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness.MackeyModule
open CategoryTheory
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C] {B : MackeyShape C}

structure Hom (M N : MackeyModule.{u,v,w} R C B) where
  app : ∀ P, M.Value P →ₗ[R] N.Value P
  pull_comm : ∀ {P Q} (f : P ⟶ Q) (x : M.Value Q), app P (M.pull f x) = N.pull f (app Q x)
  push_comm : ∀ {P Q} (f : P ⟶ Q) (x : M.Value P), app Q (M.push f x) = N.push f (app P x)

theorem hom_ext {M N : MackeyModule.{u,v,w} R C B} {f g : Hom M N}
    (h : ∀ P, f.app P = g.app P) : f = g := by
  cases f
  cases g
  congr
  exact funext h

instance : Category.{max v w} (MackeyModule.{u,v,w} R C B) where
  Hom := Hom
  id M := { app _ := LinearMap.id, pull_comm _ _ := rfl, push_comm _ _ := rfl }
  comp f g :=
    { app P := (g.app P).comp (f.app P)
      pull_comm t x := (congrArg (g.app _) (f.pull_comm t x)).trans (g.pull_comm t (f.app _ x))
      push_comm t x := (congrArg (g.app _) (f.push_comm t x)).trans (g.push_comm t (f.app _ x)) }
  id_comp f := hom_ext (fun _ => rfl)
  comp_id f := hom_ext (fun _ => rfl)
  assoc f g h := hom_ext (fun _ => rfl)

def isoOfLinearEquiv {M N : MackeyModule.{u,v,w} R C B}
    (e : ∀ P, M.Value P ≃ₗ[R] N.Value P)
    (pull : ∀ {P Q} (f : P ⟶ Q) (x : M.Value Q), e P (M.pull f x) = N.pull f (e Q x))
    (push : ∀ {P Q} (f : P ⟶ Q) (x : M.Value P), e Q (M.push f x) = N.push f (e P x)) : M ≅ N where
  hom := { app P := (e P).toLinearMap, pull_comm := pull, push_comm := push }
  inv :=
    { app P := (e P).symm.toLinearMap
      pull_comm {P Q} f x := by
        apply (e P).injective
        change (e P) ((e P).symm (N.pull f x)) = (e P) (M.pull f ((e Q).symm x))
        simpa only [LinearEquiv.apply_symm_apply] using (pull f ((e Q).symm x)).symm
      push_comm {P Q} f x := by
        apply (e Q).injective
        change (e Q) ((e Q).symm (N.push f x)) = (e Q) (M.push f ((e P).symm x))
        simpa only [LinearEquiv.apply_symm_apply] using (push f ((e P).symm x)).symm }
  hom_inv_id := by
    apply hom_ext
    intro P
    apply LinearMap.ext
    exact (e P).symm_apply_apply
  inv_hom_id := by
    apply hom_ext
    intro P
    apply LinearMap.ext
    exact (e P).apply_symm_apply

end Sharpness.MackeyModule
