import Sharpness.Mackey
import Sharpness.FiniteLength

/-! Objectwise subobjects and quotients of full Mackey coefficients.
Their full Mackey identities are proved by restriction/quotienting the
original identity; no truncated formula is introduced. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory
open scoped BigOperators

def restrictLinear {R : Type u} [Ring R]
    {A B : Type w} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (P : Submodule R A) (Q : Submodule R B)
    (h : ∀ x ∈ P, f x ∈ Q) : P →ₗ[R] Q where
  toFun x := ⟨f x.val, h x.val x.property⟩
  map_add' x y := Subtype.ext (map_add f x.val y.val)
  map_smul' a x := Subtype.ext (map_smul f a x.val)

@[simp] theorem restrictLinear_coe {R : Type u} [Ring R]
    {A B : Type w} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (P : Submodule R A) (Q : Submodule R B)
    (h : ∀ x ∈ P, f x ∈ Q) (x : P) : (restrictLinear f P Q h x).val = f x.val := rfl

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B)

def linearSystem : LinearSystem R C where
  Value := M.Value
  valueAddCommGroup := M.valueAddCommGroup
  valueModule := M.valueModule
  Operation P Q := ULift.{w} ((P ⟶ Q) ⊕ (Q ⟶ P))
  act a := Sum.elim M.push M.pull a.down

def toLinearSubsystem (N : M.Subfunctor) : M.linearSystem.Subsystem where
  obj := N.obj
  closed := by
    intro P Q a x hx
    rcases a with ⟨a⟩
    cases a with
    | inl f => exact N.push_closed f hx
    | inr f => exact N.pull_closed f hx

def submodule (N : M.Subfunctor) : MackeyModule R C B where
  Value P := N.obj P
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  pull f := restrictLinear (M.pull f) _ _ (fun _ hx => N.pull_closed f hx)
  push f := restrictLinear (M.push f) _ _ (fun _ hx => N.push_closed f hx)
  pull_id P := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (M.pull_id P) x.val
  push_id P := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (M.push_id P) x.val
  pull_comp f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (M.pull_comp f g) x.val
  push_comp f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (M.push_comp f g) x.val
  pull_iso f := by
    intro hf
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (M.pull_iso f) x.val
  mackey f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, restrictLinear_coe,
      Submodule.coe_sum] using LinearMap.congr_fun (M.mackey f g) x.val

def quotient (N : M.Subfunctor) : MackeyModule R C B where
  Value P := M.Value P ⧸ N.obj P
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  pull {P Q} f := (N.obj Q).mapQ (N.obj P) (M.pull f) (fun _ hx => N.pull_closed f hx)
  push {P Q} f := (N.obj P).mapQ (N.obj Q) (M.push f) (fun _ hx => N.push_closed f hx)
  pull_id P := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    exact congrArg (N.obj P).mkQ (LinearMap.congr_fun (M.pull_id P) y)
  push_id P := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    exact congrArg (N.obj P).mkQ (LinearMap.congr_fun (M.push_id P) y)
  pull_comp {P Q T} f g := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    exact congrArg (N.obj P).mkQ (LinearMap.congr_fun (M.pull_comp f g) y)
  push_comp {P Q T} f g := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    exact congrArg (N.obj T).mkQ (LinearMap.congr_fun (M.push_comp f g) y)
  pull_iso {P Q} f := by
    intro hf
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    exact congrArg (N.obj P).mkQ (LinearMap.congr_fun (M.pull_iso f) y)
  mackey {P Q T} f g := by
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    change (N.obj P).mkQ (M.pull f (M.push g y)) =
      ∑ i : B.Term f g, (N.obj P).mkQ
        (M.push (B.span f g i).left (M.pull (B.span f g i).right y))
    have h := congrArg (N.obj P).mkQ (LinearMap.congr_fun (M.mackey f g) y)
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum] using h

instance submodule_finite {k : Type u} [Field k] (M : MackeyModule.{u,v,w} k C B)
    (N : M.Subfunctor) [∀ P, FiniteDimensional k (M.Value P)] (P : C) :
    FiniteDimensional k ((M.submodule N).Value P) := by
  change FiniteDimensional k (N.obj P)
  infer_instance

instance quotient_finite {k : Type u} [Field k] (M : MackeyModule.{u,v,w} k C B)
    (N : M.Subfunctor) [∀ P, FiniteDimensional k (M.Value P)] (P : C) :
    FiniteDimensional k ((M.quotient N).Value P) := by
  change FiniteDimensional k (M.Value P ⧸ N.obj P)
  infer_instance

instance linearSystem_finite {k : Type u} [Field k] (M : MackeyModule.{u,v,w} k C B)
    [∀ P, FiniteDimensional k (M.Value P)] (P : C) :
    FiniteDimensional k (M.linearSystem.Value P) := by
  change FiniteDimensional k (M.Value P)
  infer_instance

/-- The finite-dimensional part of manuscript Lemma 2.4 for actual full
Mackey modules, with subobjects and quotients carrying their proved Mackey
identities. The only property-specific input is extension closure. -/
theorem finite_dimensional_reduction {k : Type u} [Field k] [Fintype C]
    (P : MackeyModule.{u,v,w} k C B → Prop)
    (zero : ∀ M [∀ i, FiniteDimensional k (M.Value i)],
      (∀ i, ∀ x : M.Value i, x = 0) → P M)
    (simple : ∀ M [∀ i, FiniteDimensional k (M.Value i)], M.IsSimple → P M)
    (extension : ∀ M [∀ i, FiniteDimensional k (M.Value i)] (N : M.Subfunctor),
      P (M.submodule N) → P (M.quotient N) → P M)
    (M : MackeyModule.{u,v,w} k C B) [∀ i, FiniteDimensional k (M.Value i)] : P M := by
  classical
  have aux : ∀ n, ∀ (A : MackeyModule.{u,v,w} k C B)
      [∀ i, FiniteDimensional k (A.Value i)], A.linearSystem.totalDimension = n → P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ hdim
      by_cases hz : ∀ i, ∀ x : A.Value i, x = 0
      · exact zero A hz
      by_cases hs : A.IsSimple
      · exact simple A hs
      have hnz : ∃ i, ∃ x : A.Value i, x ≠ 0 := by push Not at hz; exact hz
      have hn : ¬ ∀ N : A.Subfunctor,
          (∀ i, N.obj i = ⊥) ∨ (∀ i, N.obj i = ⊤) := by
        intro h
        exact hs ⟨hnz, h⟩
      push Not at hn
      obtain ⟨N, hnonzero, hproper⟩ := hn
      let N' := A.toLinearSubsystem N
      have hd := A.linearSystem.totalDimension_sub_add_quotient N'
      have hp := A.linearSystem.sub_totalDimension_pos N' (not_forall.mpr hnonzero)
      have hq := A.linearSystem.quotient_totalDimension_pos N' (not_forall.mpr hproper)
      change (A.submodule N).linearSystem.totalDimension +
        (A.quotient N).linearSystem.totalDimension = A.linearSystem.totalDimension at hd
      change 0 < (A.submodule N).linearSystem.totalDimension at hp
      change 0 < (A.quotient N).linearSystem.totalDimension at hq
      apply extension A N
      · exact ih (A.submodule N).linearSystem.totalDimension (by omega) (A.submodule N) rfl
      · exact ih (A.quotient N).linearSystem.totalDimension (by omega) (A.quotient N) rfl
  exact aux M.linearSystem.totalDimension M rfl

end MackeyModule
end Sharpness
