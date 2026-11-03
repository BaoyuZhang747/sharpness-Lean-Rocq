import Sharpness.Unconditional.RealizationSubdivisionFaces

/-! The actual monotone-complement decomposition of a permutation by its last
value, and the sign identity for the outer face of barycentric subdivision. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open Equiv

def subdivisionOuterPermutation {n : ℕ} (p : Perm (Fin (n + 1))) : Perm (Fin n) :=
  ((finSuccAboveEquiv (Fin.last n)).trans
    (p.subtypeEquiv (p := fun x => x ≠ Fin.last n)
      (q := fun x => x ≠ p (Fin.last n)) (fun _ => by simp))).trans
        (finSuccAboveEquiv (p (Fin.last n))).symm

theorem subdivisionOuterPermutation_succAbove {n : ℕ}
    (p : Perm (Fin (n + 1))) (k : Fin n) :
    (p (Fin.last n)).succAbove (subdivisionOuterPermutation p k) = p k.castSucc := by
  change ((finSuccAboveEquiv (p (Fin.last n))) (subdivisionOuterPermutation p k)).val = _
  simp [subdivisionOuterPermutation, finSuccAboveEquiv_apply, Fin.succAbove_last]

def subdivisionOuterAssemble {n : ℕ} (i : Fin (n + 1)) (q : Perm (Fin n)) :
    Perm (Fin (n + 1)) :=
  (finSuccEquivLast.trans q.optionCongr).trans (finSuccEquiv' i).symm

@[simp] theorem subdivisionOuterAssemble_last {n : ℕ}
    (i : Fin (n + 1)) (q : Perm (Fin n)) :
    subdivisionOuterAssemble i q (Fin.last n) = i := by
  simp [subdivisionOuterAssemble]

@[simp] theorem subdivisionOuterAssemble_castSucc {n : ℕ}
    (i : Fin (n + 1)) (q : Perm (Fin n)) (k : Fin n) :
    subdivisionOuterAssemble i q k.castSucc = i.succAbove (q k) := by
  simp [subdivisionOuterAssemble]

@[simp] theorem subdivisionOuterPermutation_assemble {n : ℕ}
    (i : Fin (n + 1)) (q : Perm (Fin n)) :
    subdivisionOuterPermutation (subdivisionOuterAssemble i q) = q := by
  apply Equiv.ext
  intro k
  apply Fin.succAbove_right_injective (p := i)
  simpa using subdivisionOuterPermutation_succAbove (subdivisionOuterAssemble i q) k

@[simp] theorem subdivisionOuterAssemble_permutation {n : ℕ}
    (p : Perm (Fin (n + 1))) :
    subdivisionOuterAssemble (p (Fin.last n)) (subdivisionOuterPermutation p) = p := by
  apply Equiv.ext
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp
  · rw [subdivisionOuterAssemble_castSucc, subdivisionOuterPermutation_succAbove]

def subdivisionOuterEquiv (n : ℕ) :
    Perm (Fin (n + 1)) ≃ Fin (n + 1) × Perm (Fin n) where
  toFun p := (p (Fin.last n), subdivisionOuterPermutation p)
  invFun z := subdivisionOuterAssemble z.1 z.2
  left_inv p := subdivisionOuterAssemble_permutation p
  right_inv z := by simp

theorem subdivisionOuterAssemble_cycle {n : ℕ} (i : Fin (n + 1)) (q : Perm (Fin n)) :
    subdivisionOuterAssemble i q =
      Fin.cycleIcc i (Fin.last n) * finSuccEquivLast.symm.permCongr q.optionCongr := by
  apply Equiv.ext
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simpa [Perm.mul_apply, permCongr_apply] using
      (Fin.cycleIcc_of_last (Fin.le_last i)).symm
  · simp only [subdivisionOuterAssemble_castSucc, Perm.mul_apply, permCongr_apply,
      Equiv.symm_symm, finSuccEquivLast_castSucc, optionCongr_apply, Option.map_some,
      finSuccEquivLast_symm_some]
    have h := congrFun (Fin.cycleIcc_comp_succAbove i (Fin.last n) (Fin.le_last i)) (q j)
    simpa only [Function.comp_apply, Fin.succAbove_last] using h.symm

theorem subdivisionOuterAssemble_sign {n : ℕ} (i : Fin (n + 1)) (q : Perm (Fin n)) :
    ((subdivisionOuterAssemble i q).sign : ℤ) = (-1 : ℤ) ^ (n - i.val) * (q.sign : ℤ) := by
  rw [subdivisionOuterAssemble_cycle, Perm.sign_mul, Perm.sign_permCongr,
    Equiv.optionCongr_sign, Fin.sign_cycleIcc_of_le (Fin.le_last i)]
  simp

/-- The sign of the outer face agrees with the ordinary boundary sign and
the smaller barycentric-subdivision sign. -/
theorem subdivisionOuterAssemble_boundary_sign {n : ℕ}
    (i : Fin (n + 1)) (q : Perm (Fin n)) :
    ((subdivisionOuterAssemble i q).sign : ℤ) * (-1 : ℤ) ^ n =
      (-1 : ℤ) ^ i.val * (q.sign : ℤ) := by
  rw [subdivisionOuterAssemble_sign]
  have hi : i.val ≤ n := by omega
  have hpow : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - i.val) * (-1 : ℤ) ^ i.val := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hpow]
  have hs : (-1 : ℤ) ^ (n - i.val) * (-1 : ℤ) ^ (n - i.val) = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : ℤ) ^ (n - i.val) * (-1 : ℤ) ^ (n - i.val)) *
        ((-1 : ℤ) ^ i.val * (q.sign : ℤ)) := by ring
    _ = _ := by rw [hs, one_mul]

theorem subdivisionOuterPermutation_boundary_sign {n : ℕ} (p : Perm (Fin (n + 1))) :
    (p.sign : ℤ) * (-1 : ℤ) ^ n =
      (-1 : ℤ) ^ (p (Fin.last n)).val * ((subdivisionOuterPermutation p).sign : ℤ) := by
  simpa using subdivisionOuterAssemble_boundary_sign (p (Fin.last n))
    (subdivisionOuterPermutation p)

/-- Reindex the remaining outer faces by the omitted vertex and the smaller
permutation, with the ordinary boundary sign. -/
theorem subdivision_outer_face_sum {A : Type u} [AddCommGroup A]
    (n : ℕ) (F : Perm (Fin (n + 1)) → A) :
    (∑ p : Perm (Fin (n + 1)), ((p.sign : ℤ) * (-1 : ℤ) ^ n) • F p) =
      ∑ i : Fin (n + 1), ∑ q : Perm (Fin n),
        ((-1 : ℤ) ^ i.val * (q.sign : ℤ)) • F (subdivisionOuterAssemble i q) := by
  classical
  calc
    _ = ∑ z : Fin (n + 1) × Perm (Fin n),
        (((subdivisionOuterAssemble z.1 z.2).sign : ℤ) * (-1 : ℤ) ^ n) •
          F (subdivisionOuterAssemble z.1 z.2) :=
      ((subdivisionOuterEquiv n).symm.sum_comp
        (fun p => ((p.sign : ℤ) * (-1 : ℤ) ^ n) • F p)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [subdivisionOuterAssemble_boundary_sign]

end Sharpness.RealizationUnitHomology
