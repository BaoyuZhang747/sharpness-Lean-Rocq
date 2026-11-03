import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Finite permutation pairing for the internal faces of signed barycentric
subdivision. No geometric or boundary identity is assumed here. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open Equiv

def subdivisionAdjacentPair {n : ℕ} (j : Fin (n + 1))
    (p : Perm (Fin (n + 2))) : Perm (Fin (n + 2)) :=
  p * swap j.castSucc j.succ

theorem subdivisionAdjacentPair_involutive {n : ℕ} (j : Fin (n + 1)) :
    Function.Involutive (subdivisionAdjacentPair j) := by
  intro p
  ext k
  simp [subdivisionAdjacentPair]

theorem subdivisionAdjacentPair_ne {n : ℕ} (j : Fin (n + 1))
    (p : Perm (Fin (n + 2))) : subdivisionAdjacentPair j p ≠ p := by
  intro h
  have he := congrArg (fun q : Perm (Fin (n + 2)) => q j.castSucc) h
  simp only [subdivisionAdjacentPair, Perm.mul_apply, swap_apply_left] at he
  have hf := p.injective he
  have hv := congrArg Fin.val hf
  simp at hv

theorem subdivisionAdjacentPair_sign {n : ℕ} (j : Fin (n + 1))
    (p : Perm (Fin (n + 2))) :
    ((subdivisionAdjacentPair j p).sign : ℤ) = -(p.sign : ℤ) := by
  have h : j.castSucc ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  simp [subdivisionAdjacentPair, Perm.sign_mul, Perm.sign_swap h]

/-- Every internal face cancels with its adjacent-transposition mate, over
an arbitrary abelian group, including groups with torsion. -/
theorem subdivision_internal_face_sum_zero {A : Type u} [AddCommGroup A]
    {n : ℕ} (j : Fin (n + 1)) (F : Perm (Fin (n + 2)) → A)
    (hF : ∀ p, F (subdivisionAdjacentPair j p) = F p) :
    (∑ p : Perm (Fin (n + 2)), (p.sign : ℤ) • F p) = 0 := by
  apply Finset.sum_ninvolution (subdivisionAdjacentPair j)
  · intro p
    rw [subdivisionAdjacentPair_sign, hF, neg_smul, add_neg_cancel]
  · intro p _
    exact subdivisionAdjacentPair_ne j p
  · intro p
    exact Finset.mem_univ _
  · exact subdivisionAdjacentPair_involutive j

/-- Except for the deleted internal vertex, every prefix is preserved as a
set of positions by the adjacent swap. This includes empty and full prefixes. -/
theorem subdivisionAdjacentSwap_le_iff {n : ℕ} (j : Fin (n + 1))
    (c k : Fin (n + 2)) (hc : c ≠ j.castSucc) :
    swap j.castSucc j.succ k ≤ c ↔ k ≤ c := by
  by_cases hk : k = j.castSucc
  · subst k
    rw [swap_apply_left]
    have hcv : c.val ≠ j.val := by
      intro he
      exact hc (Fin.ext he)
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega
  by_cases hk' : k = j.succ
  · subst k
    rw [swap_apply_right]
    have hcv : c.val ≠ j.val := by
      intro he
      exact hc (Fin.ext he)
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [swap_apply_of_ne_of_ne hk hk']

theorem subdivisionAdjacentPair_prefix_sum {A : Type u} [AddCommMonoid A]
    {n : ℕ} (j : Fin (n + 1)) (p : Perm (Fin (n + 2)))
    (c : Fin (n + 2)) (hc : c ≠ j.castSucc) (F : Fin (n + 2) → A) :
    (∑ k ∈ Finset.Iic c, F (subdivisionAdjacentPair j p k)) =
      ∑ k ∈ Finset.Iic c, F (p k) := by
  classical
  apply Finset.sum_bij (fun k _ => swap j.castSucc j.succ k)
  · intro k hk
    simpa only [Finset.mem_Iic, subdivisionAdjacentSwap_le_iff j c k hc] using hk
  · intro k _ l _ h
    exact (swap j.castSucc j.succ).injective h
  · intro k hk
    refine ⟨swap j.castSucc j.succ k, ?_, ?_⟩
    · simpa only [Finset.mem_Iic, subdivisionAdjacentSwap_le_iff j c k hc] using hk
    · exact swap_apply_self _ _ _
  · intro k _
    rfl

end Sharpness.RealizationUnitHomology
