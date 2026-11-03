import Sharpness.Unconditional.DegreeZero
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Vanishing agrees between the project's module-valued Ext and mathlib's
derived-category Ext. In positive degrees both assertions are proved equivalent
to the same explicit cocycle lifting condition on a projective resolution. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    [EnoughProjectives C] [HasExt.{w} C]

/-- The positive-degree module-valued Ext vanishes exactly when the
derived-category Ext group has a single element. -/
theorem ext_succ_isZero_iff_subsingleton (X Y : C) (n : ℕ) :
    IsZero (((Ext R C (n + 1)).obj (op X)).obj Y) ↔
      Subsingleton (Abelian.Ext.{w} X Y (n + 1)) := by
  let P := projectiveResolution X
  have hzero : IsZero (((Ext R C (n + 1)).obj (op X)).obj Y) ↔
      IsZero ((P.complex.linearYonedaObj R Y).homology (n + 1)) :=
    ⟨fun h => IsZero.of_iso h (P.isoExt (R := R) (n + 1) Y).symm,
      fun h => IsZero.of_iso h (P.isoExt (R := R) (n + 1) Y)⟩
  rw [hzero, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change (∀ (f : P.complex.X (n + 1) ⟶ Y),
    P.complex.d (n + 2) (n + 1) ≫ f = 0 →
      ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f) ↔ _
  constructor
  · intro h
    apply subsingleton_of_forall_eq 0
    intro α
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp (h.elim _ 0)

/-- The degree-zero and positive-degree comparisons together. -/
theorem ext_isZero_iff_subsingleton (X Y : C) (n : ℕ) :
    IsZero (((Ext R C n).obj (op X)).obj Y) ↔
      Subsingleton (Abelian.Ext.{w} X Y n) := by
  cases n with
  | zero =>
    have hzero : IsZero (((Ext R C 0).obj (op X)).obj Y) ↔
        IsZero (ModuleCat.of R (X ⟶ Y)) :=
      ⟨fun h => IsZero.of_iso h (extZeroHomIso R X Y).symm,
        fun h => IsZero.of_iso h (extZeroHomIso R X Y)⟩
    rw [hzero, ModuleCat.isZero_iff_subsingleton]
    exact Equiv.subsingleton_congr (Abelian.Ext.homEquiv₀ (X := X) (Y := Y)).symm
  | succ n => exact ext_succ_isZero_iff_subsingleton R X Y n

end Sharpness
