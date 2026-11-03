import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel

/-! The finite alternating-sum cancellation in the Alexander–Whitney boundary. -/
set_option autoImplicit false
universe u

namespace Sharpness

theorem alexanderWhitney_alternating_split {A : Type u} [AddCommGroup A]
    (p q n : ℕ) (h : p + q = n)
    (a : Fin (n + 2) → A) (b : Fin (p + 2) → A) (c : Fin (q + 2) → A)
    (hearly : ∀ i : Fin (p + 1), a ⟨i.val, by omega⟩ = b i.castSucc)
    (hlate : ∀ j : Fin (q + 1), a ⟨p + 1 + j.val, by omega⟩ = c j.succ)
    (hmiddle : b (Fin.last (p + 1)) = c 0) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • b i) +
        (-1 : ℤ) ^ p • ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • c j := by
  have hn : n + 2 = (p + 1) + (q + 1) := by omega
  have hs := Fin.sum_univ_add (a := p + 1) (b := q + 1)
    (fun i => (-1 : ℤ) ^ i.val • a (i.cast hn.symm))
  have hearly' : ∀ i : Fin (p + 1),
      a ((Fin.castAdd (q + 1) i).cast hn.symm) = b i.castSucc := by
    intro i
    exact hearly i
  have hlate' : ∀ j : Fin (q + 1),
      a ((Fin.natAdd (p + 1) j).cast hn.symm) = c j.succ := by
    intro j
    exact hlate j
  have ht : (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • b i.castSucc) +
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • c j.succ := by
    rw [← Fin.sum_congr' (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • a i) hn.symm]
    simpa only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, hearly', hlate'] using hs
  have hb := Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val • b i)
  have hc := Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • c j)
  rw [ht, hb, hc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, smul_add, Finset.smul_sum, smul_smul, hmiddle]
  have hp : (-1 : ℤ) ^ (p + 1) = -((-1 : ℤ) ^ p) := by simp [pow_succ]
  have he : ∀ j : Fin (q + 1),
      (-1 : ℤ) ^ (p + 1 + j.val) = (-1 : ℤ) ^ p * (-1 : ℤ) ^ (j.val + 1) := by
    intro j
    rw [← pow_add]
    congr 1
    omega
  simp only [hp, neg_smul, he]
  abel

end Sharpness
