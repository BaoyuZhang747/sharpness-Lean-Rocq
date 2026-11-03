import Sharpness.Unconditional.RealizationUnitHomologyAffineNaturality

/-! Coordinate and face identities for actual barycentric subdivision cells. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open Simplicial Opposite
open scoped BigOperators

/-- The barycenter of a permutation prefix has its literal uniform coordinates. -/
theorem prefixBarycenter_apply {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (k i : Fin (n + 1)) :
    prefixBarycenter p k i =
      if (p.symm i).val ≤ k.val then ((k.val + 1 : ℝ)⁻¹) else 0 := by
  classical
  let f : Fin (k.val + 1) → Fin (n + 1) := fun j =>
    p ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
  change FunOnFinite.linearMap ℝ ℝ f _ i = _
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases h : (p.symm i).val ≤ k.val
  · let j : Fin (k.val + 1) := ⟨(p.symm i).val, by omega⟩
    have hf : f j = i := by simp [f, j]
    have hi : Function.Injective f := by
      intro a b hab
      have hab' := congrArg Fin.val (p.injective hab)
      exact Fin.ext hab'
    have hfilter : Finset.univ.filter (fun a => f a = i) = {j} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun ha => hi (ha.trans hf.symm), fun ha => ha ▸ hf⟩
    rw [hfilter]
    simp [h, _root_.stdSimplex.barycenter]
    rfl
  · have hfilter : Finset.univ.filter (fun a => f a = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hai := (Finset.mem_filter.mp ha).2
      have heq : p.symm i = ⟨a.val, lt_of_lt_of_le a.isLt
          (Nat.succ_le_of_lt k.isLt)⟩ := by
        simpa [f] using congrArg p.symm hai.symm
      have hav := congrArg Fin.val heq
      exact h (by dsimp at hav; omega)
    rw [hfilter]
    simp [h]

/-- Two permutation prefixes with the same support have the same barycenter. -/
theorem prefixBarycenter_eq_of_support {n : ℕ}
    (p q : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1))
    (h : ∀ i, (p.symm i).val ≤ k.val ↔ (q.symm i).val ≤ k.val) :
    prefixBarycenter p k = prefixBarycenter q k := by
  apply Subtype.ext
  funext i
  change prefixBarycenter p k i = prefixBarycenter q k i
  simp only [prefixBarycenter_apply]
  simp only [h i]

/-- An adjacent transposition preserves each prefix other than the intervening one. -/
theorem prefixBarycenter_adjacent_swap {n : ℕ}
    (p : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) (k : Fin (n + 2))
    (hk : k ≠ j.castSucc) :
    prefixBarycenter (p * Equiv.swap j.castSucc j.succ) k = prefixBarycenter p k := by
  apply prefixBarycenter_eq_of_support
  intro i
  change (Equiv.swap j.castSucc j.succ (p.symm i)).val ≤ k.val ↔ _
  rw [Equiv.swap_apply_def]
  split_ifs with hi hi
  · rw [hi]
    have hkv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · rw [hi]
    have hkv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · rfl

/-- The paired barycentric cells have literally the same internal face. -/
theorem barycentricCell_internal_face {n : ℕ}
    (p : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (barycentricCell (p * Equiv.swap j.castSucc j.succ)).comp
        ⟨_root_.stdSimplex.map j.castSucc.succAbove,
          _root_.stdSimplex.continuous_map j.castSucc.succAbove⟩ =
      (barycentricCell p).comp
        ⟨_root_.stdSimplex.map j.castSucc.succAbove,
          _root_.stdSimplex.continuous_map j.castSucc.succAbove⟩ := by
  simp only [barycentricCell, affineSimplexMap_index]
  congr 1
  funext k
  exact prefixBarycenter_adjacent_swap p j _ (Fin.succAbove_ne _ _)

/-- The corresponding internal faces agree as actual singular simplices. -/
theorem singularBarycentricCell_internal_face {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌))
    (p : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ j.castSucc
        (singularBarycentricCell σ (p * Equiv.swap j.castSucc j.succ)) =
      (TopCat.toSSet.obj X).δ j.castSucc (singularBarycentricCell σ p) := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  simp only [TopCat.toSSetObjEquiv_δ_apply, singularBarycentricCell,
    singularAffinePull_apply]
  apply congrArg (X.toSSetObjEquiv _ σ)
  exact congrArg (fun f => f t) (barycentricCell_internal_face p j)

end Sharpness.RealizationUnitHomology
