import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-! Eventual membership under an invariant linear operator. The span lemma
turns eventual smallness of generators into eventual smallness of every chain;
the finite-set lemma provides one bound for finitely many chains at once. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.SmallChainComparison
variable {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable (f : Module.End R M) (P : Submodule R M)
variable (hP : ∀ x ∈ P, f x ∈ P)
include hP

theorem pow_mem_of_mem (n : ℕ) {x : M} (hx : x ∈ P) : (f^n) x ∈ P := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hP _ ih

theorem pow_mem_of_le {n m : ℕ} (hnm : n ≤ m) {x : M} (hx : (f^n) x ∈ P) :
    (f^m) x ∈ P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, pow_add, Module.End.mul_apply]
  exact pow_mem_of_mem f P hP k hx

/-- Eventual membership in an invariant submodule is itself a submodule. -/
def eventualSubmodule : Submodule R M where
  carrier := {x | ∃ n : ℕ, (f^n) x ∈ P}
  zero_mem' := ⟨0, by simpa using P.zero_mem⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n+m, ?_⟩
    rw [map_add]
    exact P.add_mem (pow_mem_of_le f P hP (by omega) hn)
      (pow_mem_of_le f P hP (by omega) hm)
  smul_mem' := by
    rintro a x ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [map_smul]
    exact P.smul_mem a hn

theorem eventually_mem_of_mem_span {s : Set M}
    (hs : ∀ x ∈ s, ∃ n : ℕ, (f^n) x ∈ P) {x : M}
    (hx : x ∈ Submodule.span R s) : ∃ n : ℕ, (f^n) x ∈ P := by
  have h : Submodule.span R s ≤ eventualSubmodule f P hP :=
    Submodule.span_le.mpr hs
  exact h hx

theorem eventually_mem_of_span_eq_top {s : Set M}
    (hs : ∀ x ∈ s, ∃ n : ℕ, (f^n) x ∈ P)
    (hspan : Submodule.span R s = ⊤) (x : M) : ∃ n : ℕ, (f^n) x ∈ P := by
  apply eventually_mem_of_mem_span f P hP hs
  rw [hspan]
  trivial

/-- One iterate bound works for a finite family, and every larger iterate. -/
theorem eventually_mem_finset (s : Finset M)
    (hs : ∀ x ∈ s, ∃ n : ℕ, (f^n) x ∈ P) :
    ∃ n : ℕ, ∀ m, n ≤ m → ∀ x ∈ s, (f^m) x ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨n, hn⟩ := hs x (Finset.mem_insert_self _ _)
      obtain ⟨m, hm⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
      refine ⟨n+m, ?_⟩
      intro k hk y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact pow_mem_of_le f P hP (by omega) hn
      · exact hm k (by omega) y hy

end Sharpness.SmallChainComparison
