import Sharpness.GroupNerveTuples
import Sharpness.GroupCohomologyCoefficientMaps

/-! The actual nerve face maps have precisely the inhomogeneous
group-cochain coordinates, including the order of multiplication. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Simplicial Opposite
variable {G H : Type u} [Group G] [Group H]

theorem nerveArrow_congr {m : ℕ} (x : ComposableArrows (SingleObj G) m)
    {a b c d : ℕ} {hab : a ≤ b} {hbm : b ≤ m} {hcd : c ≤ d} {hdm : d ≤ m}
    (ha : a = c) (hb : b = d) :
    x.map' a b hab hbm = x.map' c d hcd hdm := by
  subst c
  subst d
  rfl

theorem nerveTuple_map (f : G →* H) (n : ℕ)
    (x : (nerve (SingleObj G)).obj (op ⦋n⦌)) :
    nerveTuple H n ((nerveMap f.toFunctor).app _ x) = f ∘ nerveTuple G n x := by
  funext i
  change (f (x.map' i.val (i.val + 1) (Nat.le_succ i.val)
    (Nat.succ_le_of_lt i.isLt)))⁻¹ =
      f ((x.map' i.val (i.val + 1) (Nat.le_succ i.val)
        (Nat.succ_le_of_lt i.isLt))⁻¹)
  exact (map_inv f _).symm

theorem nerveTuple_face_apply (n : ℕ)
    (x : (nerve (SingleObj G)).obj (op ⦋n + 1⦌))
    (i : Fin (n + 2)) (k : Fin n) :
    nerveTuple G n ((nerve (SingleObj G)).δ i x) k =
      (x.map' (i.succAbove k.castSucc).val (i.succAbove k.succ).val
        ((Fin.succAboveOrderEmb i).monotone (show k.castSucc ≤ k.succ from
          Nat.le_succ k.val))
        (Nat.le_of_lt_succ (i.succAbove k.succ).isLt))⁻¹ := rfl

theorem nerveTuple_face_zero (n : ℕ)
    (x : (nerve (SingleObj G)).obj (op ⦋n + 1⦌)) :
    nerveTuple G n ((nerve (SingleObj G)).δ (0 : Fin (n+2)) x) =
      fun k => nerveTuple G (n+1) x k.succ := by
  funext k
  rw [nerveTuple_face_apply]
  simp only [Fin.succAbove_zero]
  rfl

theorem nerveTuple_face_succ (n : ℕ)
    (x : (nerve (SingleObj G)).obj (op ⦋n + 1⦌)) (j : Fin (n + 1)) :
    nerveTuple G n ((nerve (SingleObj G)).δ j.succ x) =
      Fin.contractNth j (· * ·) (nerveTuple G (n+1) x) := by
  change ComposableArrows (SingleObj G) (n + 1) at x
  funext k
  rw [nerveTuple_face_apply]
  rcases lt_trichotomy k.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt j (· * ·) _ k h]
    have h₀ : j.succ.succAbove k.castSucc = k.castSucc.castSucc := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h, Nat.le_of_lt h]
    have h₁ : j.succ.succAbove k.succ = k.succ.castSucc := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h]
    apply congrArg (fun a : G => a⁻¹)
    exact nerveArrow_congr x (congrArg Fin.val h₀) (congrArg Fin.val h₁)
  · rw [Fin.contractNth_apply_of_eq j (· * ·) _ k h]
    have h₀ : j.succ.succAbove k.castSucc = k.castSucc.castSucc := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h]
    have h₁ : j.succ.succAbove k.succ = k.succ.succ := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h]
    have hk : k.val + 2 ≤ n + 1 := by omega
    calc
      _ = (x.map' k.val (k.val + 2) (by omega) hk)⁻¹ :=
        congrArg (fun a : G => a⁻¹)
          (nerveArrow_congr x (a := (j.succ.succAbove k.castSucc).val)
            (b := (j.succ.succAbove k.succ).val) (c := k.val) (d := k.val + 2)
            (congrArg Fin.val h₀) (congrArg Fin.val h₁))
      _ = _ := by
        rw [x.map'_comp k.val (k.val+1) (k.val+2) (by omega) (by omega) hk,
          SingleObj.comp_as_mul, mul_inv_rev]
        rfl
  · rw [Fin.contractNth_apply_of_gt j (· * ·) _ k h]
    have h₀ : j.succ.succAbove k.castSucc = k.castSucc.succ := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h, Nat.not_le_of_gt h]
    have h₁ : j.succ.succAbove k.succ = k.succ.succ := by
      apply Fin.ext
      simp [Fin.succAbove, Fin.le_def, Fin.lt_def, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
    apply congrArg (fun a : G => a⁻¹)
    exact nerveArrow_congr x (congrArg Fin.val h₀) (congrArg Fin.val h₁)

end Sharpness.OrdinaryCohomology
