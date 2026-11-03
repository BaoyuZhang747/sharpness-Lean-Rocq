import Sharpness.SpectralSequenceVanishing

/-! Positive-column vanishing propagates through an actual first-quadrant
spectral sequence. Differentials into column zero vanish for shape reasons;
when the other columns vanish, the outgoing differentials vanish too. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

theorem spectralSequence_positive_columns_zero
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (zero : ∀ pq : ℕ × ℕ, 0 < pq.1 → IsZero ((E.page 2).X pq)) :
    ∀ (r : ℕ) (pq : ℕ × ℕ), 0 < pq.1 →
      IsZero ((E.page (r+2) (by omega)).X pq) := by
  intro r
  induction r with
  | zero => exact zero
  | succ r ih =>
    intro pq hp
    have hz : IsZero ((E.page (r+2) (by omega)).homology pq) :=
      (HomologicalComplex.ExactAt.of_isZero (ih pq hp)).isZero_homology
    exact IsZero.of_iso hz (E.iso (r+2) ((r+1 : ℕ)+2) pq (by omega) (by omega)).symm

theorem spectralSequence_d_to_column_zero
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (r n : ℕ) (pq : ℕ × ℕ) : (E.page (r+2) (by omega)).d pq (0,n) = 0 := by
  apply (E.page (r+2) (by omega)).shape
  simp only [ComplexShape.spectralSequenceNat_rel_iff]
  omega

theorem spectralSequence_d_zero_of_column_zero
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (zero : ∀ pq : ℕ × ℕ, 0 < pq.1 → IsZero ((E.page 2).X pq))
    (r : ℕ) (pq ab : ℕ × ℕ) : (E.page (r+2) (by omega)).d pq ab = 0 := by
  by_cases hp : 0 < pq.1
  · exact (spectralSequence_positive_columns_zero E zero r pq hp).eq_of_src _ _
  by_cases ha : 0 < ab.1
  · exact (spectralSequence_positive_columns_zero E zero r ab ha).eq_of_tgt _ _
  apply (E.page (r+2) (by omega)).shape
  simp only [ComplexShape.spectralSequenceNat_rel_iff]
  omega

end Sharpness
