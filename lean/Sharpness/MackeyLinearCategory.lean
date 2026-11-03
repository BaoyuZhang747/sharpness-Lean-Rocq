import Sharpness.MackeyCategory

/-! The actual full Mackey category is preadditive and R-linear.
All operations on its morphisms are the corresponding pointwise linear
operations and continue to commute with both structure functors. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness.MackeyModule
open CategoryTheory
variable {R : Type u} [CommRing R] {C : Type v} [Category.{v} C] {B : MackeyShape C}

def homEquivFamilies (M N : MackeyModule.{u,v,w} R C B) :
    Hom M N ≃ {a : ∀ P, M.Value P →ₗ[R] N.Value P //
      (∀ {P Q} (f : P ⟶ Q) x, a P (M.pull f x) = N.pull f (a Q x)) ∧
      (∀ {P Q} (f : P ⟶ Q) x, a Q (M.push f x) = N.push f (a P x))} where
  toFun f := ⟨f.app, f.pull_comm, f.push_comm⟩
  invFun f := ⟨f.val, f.property.1, f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance homZero (M N : MackeyModule.{u,v,w} R C B) : Zero (Hom M N) :=
  ⟨{ app _ := 0, pull_comm f x := (map_zero (N.pull f)).symm,
      push_comm f x := (map_zero (N.push f)).symm }⟩

instance homAdd (M N : MackeyModule.{u,v,w} R C B) : Add (Hom M N) :=
  ⟨fun f g =>
    { app P := f.app P + g.app P
      pull_comm t x := by simp only [LinearMap.add_apply, map_add, f.pull_comm, g.pull_comm]
      push_comm t x := by simp only [LinearMap.add_apply, map_add, f.push_comm, g.push_comm] }⟩

instance homNeg (M N : MackeyModule.{u,v,w} R C B) : Neg (Hom M N) :=
  ⟨fun f =>
    { app P := -f.app P
      pull_comm t x := by simp only [LinearMap.neg_apply, map_neg, f.pull_comm]
      push_comm t x := by simp only [LinearMap.neg_apply, map_neg, f.push_comm] }⟩

instance homSub (M N : MackeyModule.{u,v,w} R C B) : Sub (Hom M N) := ⟨fun f g => f + -g⟩

instance homSMul (M N : MackeyModule.{u,v,w} R C B) : SMul R (Hom M N) :=
  ⟨fun a f =>
    { app P := a • f.app P
      pull_comm t x := by simp only [LinearMap.smul_apply, map_smul, f.pull_comm]
      push_comm t x := by simp only [LinearMap.smul_apply, map_smul, f.push_comm] }⟩

instance homNSMul (M N : MackeyModule.{u,v,w} R C B) : SMul ℕ (Hom M N) :=
  ⟨fun a f =>
    { app P := a • f.app P
      pull_comm t x := by simp only [LinearMap.smul_apply, map_nsmul, f.pull_comm]
      push_comm t x := by simp only [LinearMap.smul_apply, map_nsmul, f.push_comm] }⟩

instance homZSMul (M N : MackeyModule.{u,v,w} R C B) : SMul ℤ (Hom M N) :=
  ⟨fun a f =>
    { app P := a • f.app P
      pull_comm t x := by simp only [LinearMap.smul_apply, map_zsmul, f.pull_comm]
      push_comm t x := by simp only [LinearMap.smul_apply, map_zsmul, f.push_comm] }⟩

instance homAddCommGroup (M N : MackeyModule.{u,v,w} R C B) : AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup (fun f : Hom M N => f.app)
    (fun _ _ h => hom_ext (fun P => congrFun h P)) rfl
    (fun _ _ => rfl) (fun _ => rfl)
    (fun f g => by funext P; exact (sub_eq_add_neg (f.app P) (g.app P)).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance homModule (M N : MackeyModule.{u,v,w} R C B) : Module R (Hom M N) where
  one_smul f := hom_ext (fun _ => one_smul _ _)
  mul_smul a b f := hom_ext (fun _ => mul_smul _ _ _)
  smul_add a f g := hom_ext (fun _ => smul_add _ _ _)
  smul_zero a := hom_ext (fun _ => smul_zero _)
  add_smul a b f := hom_ext (fun _ => add_smul _ _ _)
  zero_smul f := hom_ext (fun _ => zero_smul _ _)

instance : Preadditive (MackeyModule.{u,v,w} R C B) where
  homGroup M N := homAddCommGroup M N
  add_comp _ _ _ f g h := hom_ext (fun _ => LinearMap.comp_add _ _ _)
  comp_add _ _ _ f g h := hom_ext (fun _ => LinearMap.add_comp _ _ _)

instance : CategoryTheory.Linear R (MackeyModule.{u,v,w} R C B) where
  homModule M N := homModule M N
  smul_comp _ _ _ a f g := hom_ext (fun _ => LinearMap.comp_smul _ _ _)
  comp_smul _ _ _ f a g := hom_ext (fun _ => LinearMap.smul_comp _ _ _)

@[simp] theorem zero_app {M N : MackeyModule.{u,v,w} R C B} (P : C) :
    (0 : M ⟶ N).app P = 0 := rfl
@[simp] theorem add_app {M N : MackeyModule.{u,v,w} R C B} (f g : M ⟶ N) (P : C) :
    (f + g).app P = f.app P + g.app P := rfl
@[simp] theorem smul_app {M N : MackeyModule.{u,v,w} R C B} (a : R) (f : M ⟶ N) (P : C) :
    (a • f).app P = a • f.app P := rfl

end Sharpness.MackeyModule
