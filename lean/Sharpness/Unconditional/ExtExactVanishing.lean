import Sharpness.Unconditional.ExtVanishingComparison

/-! Short-exact-sequence propagation of vanishing for the module-valued Ext
used in the sharpness proof. These follow from the derived-category long exact
sequence and the proved comparison of vanishing. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    [EnoughProjectives C]

/-- Vanishing is closed under extensions, in each fixed degree. -/
theorem ext_isZero_of_shortExact (X : C) (S : ShortComplex C) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Ext R C n).obj (op X)).obj S.X₁))
    (h₃ : IsZero (((Ext R C n).obj (op X)).obj S.X₃)) :
    IsZero (((Ext R C n).obj (op X)).obj S.X₂) := by
  letI : HasExt.{u} C := hasExt_of_enoughProjectives.{u, u, v} C
  have e₁ := (ext_isZero_iff_subsingleton R X S.X₁ n).mp h₁
  have e₃ := (ext_isZero_iff_subsingleton R X S.X₃ n).mp h₃
  apply (ext_isZero_iff_subsingleton R X S.X₂ n).mpr
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨β, hβ⟩ := Abelian.Ext.covariant_sequence_exact₂ X hS α (e₃.elim _ 0)
  rw [e₁.elim β 0, Abelian.Ext.zero_comp] at hβ
  exact hβ.symm

/-- An Ext-acyclic kernel allows vanishing to pass from the middle object to
the quotient; only the next degree of the kernel is required. -/
theorem ext_isZero_quotient_of_shortExact (X : C) (S : ShortComplex C) (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero (((Ext R C (n + 1)).obj (op X)).obj S.X₁))
    (h₂ : IsZero (((Ext R C n).obj (op X)).obj S.X₂)) :
    IsZero (((Ext R C n).obj (op X)).obj S.X₃) := by
  letI : HasExt.{u} C := hasExt_of_enoughProjectives.{u, u, v} C
  have e₁ := (ext_isZero_iff_subsingleton R X S.X₁ (n + 1)).mp h₁
  have e₂ := (ext_isZero_iff_subsingleton R X S.X₂ n).mp h₂
  apply (ext_isZero_iff_subsingleton R X S.X₃ n).mpr
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨β, hβ⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS α rfl (e₁.elim _ 0)
  rw [e₂.elim β 0, Abelian.Ext.zero_comp] at hβ
  exact hβ.symm

/-- If the kernel has zero Ext in every degree, the middle and quotient
objects have identical vanishing behavior in every degree. -/
theorem ext_isZero_iff_of_shortExact (X : C) (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : ∀ n, IsZero (((Ext R C n).obj (op X)).obj S.X₁)) (n : ℕ) :
    IsZero (((Ext R C n).obj (op X)).obj S.X₂) ↔
      IsZero (((Ext R C n).obj (op X)).obj S.X₃) :=
  ⟨ext_isZero_quotient_of_shortExact R X S hS n (h₁ (n + 1)),
    ext_isZero_of_shortExact R X S hS n (h₁ n)⟩

end Sharpness
