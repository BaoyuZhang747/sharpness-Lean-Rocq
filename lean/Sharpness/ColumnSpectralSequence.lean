import Sharpness.ColumnSpectralCore
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-! A decreasing column spectral object with actual adjacent-relative
support gives a native first-quadrant spectral sequence, starting at E1.
The support property is a mathematical intermediate obligation, to be
proved for the actual filtered mapping cones, not a reference input.
The absence of incoming arrows is handled by the actual zero cutoff. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian.SpectralObject
open CategoryTheory.ComposableArrows
variable {C : Type u} [Category.{v} C] [Abelian C]
    (X : Abelian.SpectralObject C ℕᵒᵈ)

def columnRelative (n : ℤ) (a b : ℕ) (h : b ≤ a) : C :=
  (X.H n).obj (mk₁ (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from h)))

class ColumnSpectralSupport : Prop where
  zero_below : ∀ (a b : ℕ) (h : b ≤ a) (n : ℤ), a = b+1 → n < b →
    IsZero (columnRelative X n a b h)

instance columnSpectralCore_firstPage : columnSpectralCore.HasFirstPageComputation where
  hi₀₁ pq := (columnSpectralCore_page_one pq.1 pq.2).1
  hi₂₃ pq := (columnSpectralCore_page_one pq.1 pq.2).2

set_option backward.isDefEq.respectTransparency false in
instance columnSpectral_hasSpectralSequence [ColumnSpectralSupport X] :
    X.HasSpectralSequence columnSpectralCore where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    have hq : (pq.2 : ℤ)+1 < r := by
      by_contra hq
      apply hpq (pq.1+r.toNat, ((pq.2 : ℤ)+1-r).toNat)
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> omega
    change IsZero (columnRelative X n ((pq.1 : ℤ)+r').toNat
      ((pq.1 : ℤ)+r).toNat (by omega))
    apply ColumnSpectralSupport.zero_below
    · omega
    · dsimp [columnSpectralCore] at hn
      omega
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    have hp : (pq.1 : ℤ) < r := by
      by_contra hp
      apply hpq (((pq.1 : ℤ)-r).toNat, ((pq.2 : ℤ)+r-1).toNat)
      simp only [ComplexShape.spectralSequenceNat_rel_iff]
      constructor <;> omega
    have he : columnSpectralCore.i₃ r pq = columnSpectralCore.i₃ r' pq := by
      change ((pq.1 : ℤ)+1-r).toNat = ((pq.1 : ℤ)+1-r').toNat
      omega
    haveI := isIso_homOfLE he
    exact X.isZero_H_map_mk₁_of_isIso n _

variable [ColumnSpectralSupport X]

def columnSpectralSequence : CohomologicalSpectralSequenceNat C 1 :=
  X.spectralSequence columnSpectralCore

def columnE₂SpectralSequence : E₂CohomologicalSpectralSequenceNat C where
  page r hr := (columnSpectralSequence X).page r (by omega)
  iso r r' pq hrr' hr := (columnSpectralSequence X).iso r r' pq hrr' (by omega)

def columnSpectralSequenceFirstPageIso (p q : ℕ) :
    ((columnSpectralSequence X).page 1).X (p,q) ≅ columnRelative X (p+q) (p+1) p (by omega) :=
  X.spectralSequenceFirstPageXIso columnSpectralCore (p,q)
    (OrderDual.toDual (p+1)) (OrderDual.toDual p) rfl rfl (p+q) rfl

end Sharpness
