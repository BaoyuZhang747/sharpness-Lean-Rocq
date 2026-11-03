import Mathlib

/-! Algebraic parts of `cor:local`. Higher-limit long exact sequences and the
filtered-colimit comparison have to be instantiated separately. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness

theorem scalar_surjective_of_factorization {R : Type u} [CommRing R]
    {A : Type v} [AddCommGroup A] [Module R A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (a : A →ₗ[R] B) (b : B →ₗ[R] A) (p : R)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (factor : ∀ x, b (a x) = p • x) : Function.Surjective (fun x : A => p • x) := by
  intro x
  obtain ⟨y, hy⟩ := hb x
  obtain ⟨z, hz⟩ := ha y
  exact ⟨z, (factor z).symm.trans (by rw [hz, hy])⟩

/-- The Nakayama step: finite generation is an essential hypothesis.
No such statement is asserted for arbitrary p-divisible modules. -/
theorem zero_of_fg_of_scalar_surjective {R : Type u} [CommRing R]
    {A : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A]
    (p : R) (hp : p ∈ Ideal.jacobson (⊥ : Ideal R))
    (surj : Function.Surjective (fun x : A => p • x)) : ∀ x : A, x = 0 := by
  have hle : (⊤ : Submodule R A) ≤ (Ideal.span {p}) • (⊤ : Submodule R A) := by
    intro x _
    obtain ⟨y, rfl⟩ := surj x
    exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (Submodule.mem_top : y ∈ ⊤)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (Ideal.span {p}) (⊤ : Submodule R A) Module.Finite.fg_top hle
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))
  intro x
  have hm : x ∈ (⊥ : Submodule R A) := by rw [← hbot]; trivial
  exact hm

end Sharpness
