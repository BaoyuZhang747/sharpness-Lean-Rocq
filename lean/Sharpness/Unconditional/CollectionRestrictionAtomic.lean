import Sharpness.Unconditional.AtomicFiltration

/-! Collection restriction from atomic vanishing. The kernel of the
restriction/zero-extension unit is supported outside the collection, so
the finite atomic filtration applies to it. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.ZeroExtension
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] {C : Type u} [Category.{u} C] [Fintype C]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    (X : ObjectProperty C)
    (upward : ∀ {P Q : C}, (P ⟶ Q) → X P → X Q)

omit [Fintype C] in
theorem unitKernel_zero_on_collection (M : CoefficientCategory R C) (P : C) (hP : X P) :
    IsZero ((kernel (unitMap R X upward M)).obj (op P)) := by
  let π := unitMap R X upward M
  haveI : Mono (π.app (op P)) := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    exact congrFun hxy ⟨hP⟩)
  exact IsZero.of_iso (isZero_kernel_of_mono (π.app (op P)))
    (PreservesKernel.iso ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op P)) π)

include rank rank_mono iso_of_rank upward in
/-- Removing an upward-closed collection whose complementary atomic
diagrams are acyclic in every degree preserves higher-limit vanishing. -/
theorem isZero_higherLimit_iff_restriction
    (atomic : ∀ Q, ¬ X Q → ∀ A : CoefficientCategory R C,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (M : CoefficientCategory R C) (n : ℕ) :
    IsZero (higherLimit M n) ↔ IsZero (higherLimit (X.ι.op ⋙ M) n) := by
  classical
  let π := unitMap R X upward M
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
  have hK : ∀ n, IsZero (higherLimit (kernel π) n) :=
    AtomicFiltration.higherLimits_zero_of_atomic R rank rank_mono iso_of_rank
      (fun Q => ¬ X Q) atomic (kernel π) (by
        intro P hP
        exact unitKernel_zero_on_collection R X upward M P (not_not.mp hP))
  have he := ext_isZero_iff_of_shortExact R (constantCoefficient R C) S hS hK n
  have ei := higherLimitIso R X upward (X.ι.op ⋙ M) n
  exact he.trans ⟨fun h => IsZero.of_iso h ei.symm, fun h => IsZero.of_iso h ei⟩

include rank rank_mono iso_of_rank upward in
theorem acyclic_iff_restriction
    (atomic : ∀ Q, ¬ X Q → ∀ A : CoefficientCategory R C,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (M : CoefficientCategory R C) :
    Acyclic M ↔ Acyclic (X.ι.op ⋙ M) := by
  constructor
  · intro h n hn
    exact (isZero_higherLimit_iff_restriction R rank rank_mono iso_of_rank X upward atomic M n).mp
      (h n hn)
  · intro h n hn
    exact (isZero_higherLimit_iff_restriction R rank rank_mono iso_of_rank X upward atomic M n).mpr
      (h n hn)

end Sharpness.ZeroExtension
