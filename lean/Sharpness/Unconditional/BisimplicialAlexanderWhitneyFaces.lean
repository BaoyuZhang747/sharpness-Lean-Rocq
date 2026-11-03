import Sharpness.AlexanderWhitneyFaces

/-! Explicit simplex-category identities underlying the Alexander–Whitney
boundary identity, including the two cancelling middle terms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite

theorem alexanderWhitneyFront_face_early (p q n : ℕ) (h : p + q = n)
    (i : Fin (p + 1)) :
    alexanderWhitneyFront p q n h ≫ SimplexCategory.δ ⟨i.val, by omega⟩ =
      SimplexCategory.δ i.castSucc ≫
        alexanderWhitneyFront (p + 1) q (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe]
  change (Fin.succAbove ⟨i.val, _⟩ ⟨k.val, _⟩).val =
    (Fin.succAbove i.castSucc k).val + 0
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

theorem alexanderWhitneyBack_face_early (p q n : ℕ) (h : p + q = n)
    (i : Fin (p + 1)) :
    alexanderWhitneyBack p q n h ≫ SimplexCategory.δ ⟨i.val, by omega⟩ =
      alexanderWhitneyBack (p + 1) q (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  change (Fin.succAbove ⟨i.val, _⟩ ⟨k.val + p, _⟩).val = k.val + (p + 1)
  rw [Fin.succAbove_of_le_castSucc _ _ (by change i.val ≤ k.val + p; omega)]
  rfl

theorem alexanderWhitneyFront_face_late (p q n : ℕ) (h : p + q = n)
    (j : Fin (q + 1)) :
    alexanderWhitneyFront p q n h ≫ SimplexCategory.δ ⟨p + 1 + j.val, by omega⟩ =
      alexanderWhitneyFront p (q + 1) (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  change (Fin.succAbove ⟨p + 1 + j.val, _⟩ ⟨k.val, _⟩).val = k.val + 0
  have hk : k.val < p + 1 := k.isLt
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change k.val < p + 1 + j.val; omega)]
  rfl

theorem alexanderWhitneyBack_face_late (p q n : ℕ) (h : p + q = n)
    (j : Fin (q + 1)) :
    alexanderWhitneyBack p q n h ≫ SimplexCategory.δ ⟨p + 1 + j.val, by omega⟩ =
      SimplexCategory.δ j.succ ≫
        alexanderWhitneyBack p (q + 1) (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  change (Fin.succAbove ⟨p + 1 + j.val, _⟩ ⟨k.val + p, _⟩).val =
    (Fin.succAbove j.succ k).val + p
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem alexanderWhitneyFront_face_middle (p q n : ℕ) (h : p + q = n) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫
        alexanderWhitneyFront (p + 1) q (n + 1) (by omega) =
      alexanderWhitneyFront p (q + 1) (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  change (Fin.succAbove (Fin.last (p + 1)) k).val + 0 = k.val + 0
  have hk : k.val < p + 1 := k.isLt
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change k.val < p + 1; omega)]
  rfl

theorem alexanderWhitneyBack_face_middle (p q n : ℕ) (h : p + q = n) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫
        alexanderWhitneyBack p (q + 1) (n + 1) (by omega) =
      alexanderWhitneyBack (p + 1) q (n + 1) (by omega) := by
  ext k : 3
  apply Fin.ext
  change (Fin.succAbove (0 : Fin (q + 2)) k).val + p = k.val + (p + 1)
  rw [Fin.succAbove_of_le_castSucc _ _ (by simp)]
  change k.val + 1 + p = k.val + (p + 1)
  omega

end Sharpness
