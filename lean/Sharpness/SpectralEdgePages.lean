import Sharpness.SpectralColumnZero

/-! The actual canonical maps from later zero-column pages back to E₂.
They are defined without a vanishing hypothesis, using the cycle inclusion
and the page/homology isomorphisms, and become isomorphisms after collapse. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

def spectralZeroColumnStepBack
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R)) (r n : ℕ) :
    (E.page ((r+1 : ℕ)+2) (by omega)).X (0,n) ⟶ (E.page (r+2) (by omega)).X (0,n) :=
  (E.iso (r+2) ((r+1 : ℕ)+2) (0,n) (by omega) (by omega)).inv ≫
    (((E.page (r+2) (by omega)).sc (0,n)).asIsoHomologyπ
      (spectralSequence_d_to_column_zero E r n _)).inv ≫
    ((E.page (r+2) (by omega)).sc (0,n)).iCycles

theorem spectralZeroColumnStepBack_isIso
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (zero : ∀ pq : ℕ × ℕ, 0 < pq.1 → IsZero ((E.page 2).X pq)) (r n : ℕ) :
    IsIso (spectralZeroColumnStepBack E r n) := by
  have hg : ((E.page (r+2) (by omega)).sc (0,n)).g = 0 :=
    spectralSequence_d_zero_of_column_zero E zero r _ _
  let e := (E.iso (r+2) ((r+1 : ℕ)+2) (0,n) (by omega) (by omega)).symm ≪≫
    (((E.page (r+2) (by omega)).sc (0,n)).asIsoHomologyπ
      (spectralSequence_d_to_column_zero E r n _)).symm ≪≫
    ((E.page (r+2) (by omega)).sc (0,n)).cyclesIsoX₂ hg
  have he : e.hom = spectralZeroColumnStepBack E r n := rfl
  rw [← he]
  infer_instance

def spectralZeroColumnBack
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R)) :
    ∀ (r n : ℕ), (E.page (r+2) (by omega)).X (0,n) ⟶ (E.page 2).X (0,n)
  | 0, _ => 𝟙 _
  | r+1, n => spectralZeroColumnStepBack E r n ≫ spectralZeroColumnBack E r n

theorem spectralZeroColumnBack_isIso
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (zero : ∀ pq : ℕ × ℕ, 0 < pq.1 → IsZero ((E.page 2).X pq)) (r n : ℕ) :
    IsIso (spectralZeroColumnBack E r n) := by
  induction r with
  | zero => change IsIso (𝟙 _); infer_instance
  | succ r ih =>
    letI := ih
    letI := spectralZeroColumnStepBack_isIso E zero r n
    change IsIso (spectralZeroColumnStepBack E r n ≫ spectralZeroColumnBack E r n)
    infer_instance

end Sharpness
