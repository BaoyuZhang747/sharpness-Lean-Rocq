import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence

/-! The spectral-sequence indices for a decreasing column filtration.
Page one is vertical cohomology, and d_r has bidegree (r,1-r).
The native E2 core uses a different indexing convention, so the four
filtration indices are constructed here rather than relabelled. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Abelian.SpectralObject

set_option backward.isDefEq.respectTransparency false in
def columnSpectralCore : SpectralSequenceDataCore ℕᵒᵈ
    (fun r => ComplexShape.spectralSequenceNat (r, 1-r)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := OrderDual.toDual (((pq.1 : ℤ) + r).toNat)
  i₁ pq := OrderDual.toDual (pq.1+1)
  i₂ pq := OrderDual.toDual pq.1
  i₃ r pq _ := OrderDual.toDual (((pq.1 : ℤ) + 1 - r).toNat)
  le₀₁ r pq hr := by change pq.1+1 ≤ ((pq.1 : ℤ)+r).toNat; omega
  le₁₂ pq := by change pq.1 ≤ pq.1+1; omega
  le₂₃ r pq hr := by change ((pq.1 : ℤ)+1-r).toNat ≤ pq.1; omega
  hc r pq pq' hpq _ := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    change (pq.1 : ℤ)+pq.2+1 = (pq'.1 : ℤ)+pq'.2
    omega
  hc₀₂ r pq pq' hpq _ := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    change ((pq.1 : ℤ)+r).toNat = pq'.1
    omega
  hc₁₃ r pq pq' hpq _ := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    change pq.1+1 = ((pq'.1 : ℤ)+1-r).toNat
    omega
  antitone_i₀ r r' pq _ h := by
    change ((pq.1 : ℤ)+r).toNat ≤ ((pq.1 : ℤ)+r').toNat
    omega
  monotone_i₃ r r' pq _ h := by
    change ((pq.1 : ℤ)+1-r').toNat ≤ ((pq.1 : ℤ)+1-r).toNat
    omega
  i₀_prev r r' pq pq' hpq hrr' _ := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    change ((pq.1 : ℤ)+r').toNat = pq'.1+1
    omega
  i₃_next r r' pq pq' hpq hrr' _ := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    change ((pq'.1 : ℤ)+1-r').toNat = pq.1
    omega

theorem columnSpectralCore_page_one (p q : ℕ) :
    columnSpectralCore.i₀ 1 (p,q) = columnSpectralCore.i₁ (p,q) ∧
      columnSpectralCore.i₂ (p,q) = columnSpectralCore.i₃ 1 (p,q) := by
  constructor
  · change ((p : ℤ)+1).toNat = p+1
    omega
  · change p = ((p : ℤ)+1-1).toNat
    omega

end Sharpness
