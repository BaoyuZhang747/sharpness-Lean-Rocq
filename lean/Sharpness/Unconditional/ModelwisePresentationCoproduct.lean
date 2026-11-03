import Sharpness.Unconditional.ModelwisePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! Transport of actual model presentations through natural isomorphisms
and categorical coproducts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w r t s

namespace Sharpness.ModelPresentation
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]

/-- Transport a model-generator presentation through an actual natural isomorphism. -/
def ofIso {P Q : C ⥤ ModuleCat.{w} R} {I : Type t} {models : I → C}
    (p : ModelPresentation P models) (e : P ≅ Q) : ModelPresentation Q models where
  generator i := e.hom.app (models i) (p.generator i)
  lift F x := e.inv ≫ p.lift F x
  lift_generator F x i := by
    have he := congrArg (fun f : P ⟶ P => f.app (models i) (p.generator i)) e.hom_inv_id
    change e.inv.app (models i) (e.hom.app (models i) (p.generator i)) = p.generator i at he
    change (p.lift F x).app (models i)
      (e.inv.app (models i) (e.hom.app (models i) (p.generator i))) = x i
    rw [he]
    exact p.lift_generator F x i
  hom_ext a b h := by
    apply (cancel_epi e.hom).mp
    apply p.hom_ext
    intro i
    exact h i

/-- A coproduct of actual presentations is presented by the disjoint union
of their model generators. -/
def coproduct {J : Type s} (P : J → (C ⥤ ModuleCat.{w} R)) [HasCoproduct P]
    (I : J → Type t) (models : ∀ j, I j → C)
    (p : ∀ j, ModelPresentation (P j) (models j)) :
    ModelPresentation (∐ P) (fun x : Σ j, I j => models x.1 x.2) where
  generator x := (Sigma.ι P x.1).app (models x.1 x.2) ((p x.1).generator x.2)
  lift F x := Sigma.desc (fun j => (p j).lift F (fun i => x ⟨j, i⟩))
  lift_generator F x i := by
    have h := Sigma.ι_desc (fun j => (p j).lift F (fun k => x ⟨j, k⟩)) i.1
    have hh := congrArg
      (fun f : P i.1 ⟶ F => f.app (models i.1 i.2) ((p i.1).generator i.2)) h
    exact hh.trans ((p i.1).lift_generator F _ i.2)
  hom_ext a b h := by
    apply Sigma.hom_ext
    intro j
    apply (p j).hom_ext
    intro i
    exact h ⟨j, i⟩

/-- A coproduct of one-model presentations, retaining the original index type. -/
def coproductSingleton {J : Type s} (P : J → (C ⥤ ModuleCat.{w} R)) [HasCoproduct P]
    (models : J → C) (p : ∀ j, ModelPresentation (P j) (fun _ : Unit => models j)) :
    ModelPresentation (∐ P) models where
  generator j := (Sigma.ι P j).app (models j) ((p j).generator ())
  lift F x := Sigma.desc (fun j => (p j).lift F (fun _ => x j))
  lift_generator F x j := by
    have h := Sigma.ι_desc (fun k => (p k).lift F (fun _ => x k)) j
    have hh := congrArg (fun f : P j ⟶ F => f.app (models j) ((p j).generator ())) h
    exact hh.trans ((p j).lift_generator F _ ())
  hom_ext a b h := by
    apply Sigma.hom_ext
    intro j
    apply (p j).hom_ext
    intro i
    cases i
    exact h j

end Sharpness.ModelPresentation
