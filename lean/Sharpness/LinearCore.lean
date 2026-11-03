import Mathlib

/-!
Linear algebra used in `lem:generators`, `lem:centralizer-zero` and
`lem:simple-quotient`. This file does not assume any theorem of the manuscript.
The closure hypotheses below have to be proved from the full Mackey formula
before these lemmas can be applied to an actual Mackey functor.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness

/-- A family of modules and its specified structure operations. -/
structure LinearSystem (R : Type u) [Ring R] (I : Type v) where
  Value : I → Type w
  valueAddCommGroup : ∀ i, AddCommGroup (Value i)
  valueModule : ∀ i, Module R (Value i)
  Operation : I → I → Type (max v w)
  act : ∀ {i j}, Operation i j → Value i →ₗ[R] Value j

attribute [instance] LinearSystem.valueAddCommGroup LinearSystem.valueModule

namespace LinearSystem
variable {R : Type u} [Ring R] {I : Type v} (M : LinearSystem.{u,v,w} R I)

/-- An actual family of submodules closed under every structure operation. -/
structure Subsystem where
  obj : ∀ i, Submodule R (M.Value i)
  closed : ∀ {i j} (a : M.Operation i j) {x : M.Value i},
    x ∈ obj i → M.act a x ∈ obj j

/-- Simplicity is a property, not a field that asserts any generation theorem. -/
def IsSimple : Prop :=
  (∃ i, ∃ x : M.Value i, x ≠ 0) ∧
  ∀ N : M.Subsystem, (∀ i, N.obj i = ⊥) ∨ (∀ i, N.obj i = ⊤)

theorem subsystem_eq_top_of_nonzero (hM : M.IsSimple) (N : M.Subsystem)
    {q : I} {x : M.Value q} (hx : x ∈ N.obj q) (hne : x ≠ 0) :
    ∀ i, N.obj i = ⊤ := by
  rcases hM.2 N with h | h
  · have : x = 0 := by simpa [h q] using hx
    exact (hne this).elim
  · exact h

theorem subsystem_eq_bot_of_proper (hM : M.IsSimple) (N : M.Subsystem)
    {q : I} {x : M.Value q} (hx : x ∉ N.obj q) :
    ∀ i, N.obj i = ⊥ := by
  rcases hM.2 N with h | h
  · exact h
  · exact (hx (by simp [h q])).elim

/-- The sum of images used for the transfer-generated family J. -/
def transferSpan {J : Type v} (V : J → Type w)
    [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
    (tr : ∀ i j, V j →ₗ[R] M.Value i) (i : I) : Submodule R (M.Value i) :=
  ⨆ j, LinearMap.range (tr i j)

/-- The simplicity argument in the first half of `lem:generators`.
The full Mackey formula must supply `closed`; it is not silently discharged. -/
theorem transferSpan_eq_top {J : Type v} (V : J → Type w)
    [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
    (tr : ∀ i j, V j →ₗ[R] M.Value i)
    (closed : ∀ {i i'} (a : M.Operation i i') {x : M.Value i},
      x ∈ M.transferSpan V tr i → M.act a x ∈ M.transferSpan V tr i')
    (hM : M.IsSimple) {q : I} {j : J} {y : V j} (hy : tr q j y ≠ 0) :
    ∀ i, M.transferSpan V tr i = ⊤ := by
  let N : M.Subsystem := ⟨M.transferSpan V tr, closed⟩
  apply M.subsystem_eq_top_of_nonzero hM N (q := q) (x := tr q j y) _ hy
  exact le_iSup (fun j => LinearMap.range (tr q j)) j ⟨y, rfl⟩

/-- The intersection of kernels used for the detecting family K. -/
def restrictionKernel {J : Type v} (V : J → Type w)
    [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
    (res : ∀ i j, M.Value i →ₗ[R] V j) (i : I) : Submodule R (M.Value i) :=
  ⨅ j, LinearMap.ker (res i j)

theorem restrictionKernel_eq_bot {J : Type v} (V : J → Type w)
    [∀ j, AddCommGroup (V j)] [∀ j, Module R (V j)]
    (res : ∀ i j, M.Value i →ₗ[R] V j)
    (closed : ∀ {i i'} (a : M.Operation i i') {x : M.Value i},
      x ∈ M.restrictionKernel V res i → M.act a x ∈ M.restrictionKernel V res i')
    (hM : M.IsSimple) {q : I} {j : J} {x : M.Value q} (hx : res q j x ≠ 0) :
    ∀ i, M.restrictionKernel V res i = ⊥ := by
  let N : M.Subsystem := ⟨M.restrictionKernel V res, closed⟩
  apply M.subsystem_eq_bot_of_proper hM N (q := q) (x := x)
  intro hm
  have := (iInf_le (fun j => LinearMap.ker (res q j)) j) hm
  exact hx this

end LinearSystem

section Detection
variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
    {I : Type w} {B : I → Type v} [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]

/-- The componentwise restriction map is an actual linear map into a product. -/
def restrictionProduct (res : ∀ i, A →ₗ[R] B i) : A →ₗ[R] ∀ i, B i :=
  LinearMap.pi res

theorem restrictionProduct_injective_iff (res : ∀ i, A →ₗ[R] B i) :
    Function.Injective (restrictionProduct res) ↔
      ∀ x : A, (∀ i, res i x = 0) → x = 0 := by
  constructor
  · intro h x hx
    apply h
    funext i
    exact (hx i).trans (map_zero (res i)).symm
  · intro h x y hxy
    have hz : x - y = 0 := h (x - y) (fun i => by
      have hi := congrFun hxy i
      change res i x = res i y at hi
      simp only [map_sub, hi, sub_self])
    exact sub_eq_zero.mp hz

theorem linearMap_eq_zero_of_spanning_ranges (res : A →ₗ[R] A)
    (tr : ∀ i, B i →ₗ[R] A)
    (generates : (⨆ i, LinearMap.range (tr i)) = ⊤)
    (kills : ∀ i, res.comp (tr i) = 0) : res = 0 := by
  have hle : (⨆ i, LinearMap.range (tr i)) ≤ LinearMap.ker res := by
    refine iSup_le fun i x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    have h := LinearMap.congr_fun (kills i) y
    exact h
  ext x
  exact hle (by simp [generates])

/-- The same argument with an arbitrary restriction codomain. -/
theorem restriction_eq_zero_of_transfer_generation
    {C : Type v} [AddCommGroup C] [Module R C] (res : A →ₗ[R] C)
    (tr : ∀ i, B i →ₗ[R] A)
    (generates : (⨆ i, LinearMap.range (tr i)) = ⊤)
    (kills : ∀ i, res.comp (tr i) = 0) : res = 0 := by
  have hle : (⨆ i, LinearMap.range (tr i)) ≤ LinearMap.ker res := by
    refine iSup_le fun i x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact LinearMap.congr_fun (kills i) y
  ext x
  exact hle (by simp [generates])

/-- `lem:simple-quotient`, Step 2: restriction detection lifts triviality of an
automorphism from the minimal values to the entire value. -/
theorem action_eq_id_of_detected (res : ∀ i, A →ₗ[R] B i)
    (detects : Function.Injective (restrictionProduct res)) (a : A →ₗ[R] A)
    (componentwise : ∀ i, (res i).comp a = res i) : a = LinearMap.id := by
  ext x
  apply detects
  funext i
  exact LinearMap.congr_fun (componentwise i) x

end Detection
end Sharpness
