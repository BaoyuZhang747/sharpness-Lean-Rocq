import Sharpness.FirstQuadrantFilteredCochains
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! The actual filtered complexes are strictly supported in degrees at
least their column index. This supplies first-quadrant support for the
mapping-cone spectral object, rather than assuming vanishing of pages. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem totalColumnFiltration_eq_bot_of_lt (k n : ℕ) (hn : n < k) :
    totalColumnFiltration K k n = ⊥ := by
  apply le_bot_iff.mp
  calc
    totalColumnFiltration K k n ≤ totalColumnFiltration K (n+1) n :=
      totalColumnFiltration_antitone K n (by omega)
    _ = ⊥ := totalColumnFiltration_stop K n

theorem totalColumnFilteredComplex_term_zero (k n : ℕ) (hn : n < k) :
    IsZero ((totalColumnFilteredComplex K k).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  apply Subtype.ext
  have he := congrArg (fun W : Submodule R ((K.total (ComplexShape.up ℕ)).X n) =>
    x.val ∈ W) (totalColumnFiltration_eq_bot_of_lt K k n hn)
  exact Eq.mp he x.property

def totalColumnFilteredExtended (k : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (totalColumnFilteredComplex K k).extend ComplexShape.embeddingUpNat

theorem totalColumnFilteredExtended_isStrictlyGE (k : ℕ) :
    (totalColumnFilteredExtended K k).IsStrictlyGE (k : ℤ) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).mpr
  intro i hi
  by_cases h : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact IsZero.of_iso (totalColumnFilteredComplex_term_zero K k n (by omega))
      ((totalColumnFilteredComplex K k).extendXIso ComplexShape.embeddingUpNat rfl)
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i (by
      intro n hn
      change (n : ℤ) = i at hn
      omega)

end Sharpness
