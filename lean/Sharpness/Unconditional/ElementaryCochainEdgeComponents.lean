import Sharpness.ZeroColumnTotalProjection

/-! Finite diagonals and the actual signed incoming differentials of the
native nonnegative cochain total complex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped BigOperators
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem projection_sum (n : ℕ) :
    (∑ i : Fin (n + 1), totalSummandProjectionAt K i.val (n-i.val) n (by omega) ≫
      K.ιTotal (ComplexShape.up ℕ) i.val (n-i.val) n
        (by change i.val+(n-i.val)=n; omega)) =
      𝟙 ((K.total (ComplexShape.up ℕ)).X n) := by
  classical
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=n at hpq
  rw [comp_sum, Category.comp_id]
  let k : Fin (n+1) := ⟨p, by omega⟩
  rw [Finset.sum_eq_single k]
  · have hq : n-p=q := by omega
    subst q
    dsimp only [k]
    rw [← Category.assoc, totalSummandProjectionAt_inclusion, Category.id_comp]
  · intro i _ hi
    have hip : p ≠ i.val := fun he => hi (Fin.ext he.symm)
    rw [← Category.assoc, totalSummandProjectionAt_other K i.val (n-i.val) n p q
      (by omega) hpq hip, zero_comp]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem element_decomposition {n : ℕ} (x : (K.total (ComplexShape.up ℕ)).X n) :
    (∑ i : Fin (n+1), K.ιTotal (ComplexShape.up ℕ) i.val (n-i.val) n
      (by change i.val+(n-i.val)=n; omega)
      (totalSummandProjectionAt K i.val (n-i.val) n (by omega) x)) = x := by
  have h := congrArg (fun f : (K.total (ComplexShape.up ℕ)).X n ⟶
      (K.total (ComplexShape.up ℕ)).X n => f.hom x) (projection_sum K n)
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

theorem element_ext {n : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (h : ∀ p q (hpq : p+q=n), totalSummandProjectionAt K p q n hpq x =
      totalSummandProjectionAt K p q n hpq y) : x=y := by
  rw [← element_decomposition K x, ← element_decomposition K y]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i.val (n-i.val)]

theorem horizontal_outgoing (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ K.D₁ (ComplexShape.up ℕ) n (n+1) =
      (K.d p (p+1)).f q ≫ K.ιTotal (ComplexShape.up ℕ) (p+1) q (n+1)
        (by change p+1+q=n+1; omega) := by
  rw [HomologicalComplex₂.ι_D₁, HomologicalComplex₂.d₁_eq K (ComplexShape.up ℕ)
    (show (ComplexShape.up ℕ).Rel p (p+1) from rfl) q (n+1)
      (by change p+1+q=n+1; omega)]
  exact one_smul _ _

theorem vertical_outgoing (p q n : ℕ) (h : p+q=n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ K.D₂ (ComplexShape.up ℕ) n (n+1) =
      (-1 : ℤˣ)^p • ((K.X p).d q (q+1) ≫
        K.ιTotal (ComplexShape.up ℕ) p (q+1) (n+1)
          (by change p+(q+1)=n+1; omega)) := by
  rw [HomologicalComplex₂.ι_D₂, HomologicalComplex₂.d₂_eq K (ComplexShape.up ℕ) p
    (show (ComplexShape.up ℕ).Rel q (q+1) from rfl) (n+1)
      (by change p+(q+1)=n+1; omega)]
  rfl

theorem horizontal_incoming (p q n : ℕ) (h : p+q=n) :
    K.D₁ (ComplexShape.up ℕ) n (n+1) ≫
      totalSummandProjectionAt K (p+1) q (n+1) (by omega) =
      totalSummandProjectionAt K p q n h ≫ (K.d p (p+1)).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, horizontal_outgoing K i j n hij, Category.assoc]
  by_cases hi : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    rw [totalSummandProjectionAt_inclusion, Category.comp_id, ← Category.assoc,
      totalSummandProjectionAt_inclusion, Category.id_comp]
  · rw [totalSummandProjectionAt_other K (p+1) q (n+1) (i+1) j
      (by omega) (by omega) (by omega), comp_zero, ← Category.assoc,
      totalSummandProjectionAt_other K p q n i j h hij hi, zero_comp]

theorem horizontal_incoming_zero (n : ℕ) :
    K.D₁ (ComplexShape.up ℕ) n (n+1) ≫
      totalSummandProjectionAt K 0 (n+1) (n+1) (by omega) = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, horizontal_outgoing K i j n hij, Category.assoc,
    totalSummandProjectionAt_other K 0 (n+1) (n+1) (i+1) j
      (by omega) (by omega) (by omega), comp_zero, comp_zero]

theorem vertical_incoming (p q n : ℕ) (h : p+q=n) :
    K.D₂ (ComplexShape.up ℕ) n (n+1) ≫
      totalSummandProjectionAt K p (q+1) (n+1) (by omega) =
      (-1 : ℤˣ)^p • (totalSummandProjectionAt K p q n h ≫ (K.X p).d q (q+1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, vertical_outgoing K i j n hij, Linear.units_smul_comp,
    Category.assoc, Linear.comp_units_smul]
  by_cases hi : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    rw [totalSummandProjectionAt_inclusion, ← Category.assoc, totalSummandProjectionAt_inclusion,
      Category.comp_id, Category.id_comp]
  · rw [totalSummandProjectionAt_other K p (q+1) (n+1) i (j+1)
      (by omega) (by omega) hi, comp_zero, ← Category.assoc,
      totalSummandProjectionAt_other K p q n i j h hij hi, zero_comp, smul_zero, smul_zero]

theorem vertical_incoming_zero (n : ℕ) :
    K.D₂ (ComplexShape.up ℕ) n (n+1) ≫
      totalSummandProjectionAt K (n+1) 0 (n+1) (by omega) = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  rw [← Category.assoc, vertical_outgoing K i j n hij, Linear.units_smul_comp,
    Category.assoc, totalSummandProjectionAt_other K (n+1) 0 (n+1) i (j+1)
      (by omega) (by omega) (by omega), comp_zero, smul_zero, comp_zero]

theorem differential_component (p q n : ℕ) (h : p+(q+1)=n)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    totalSummandProjectionAt K (p+1) (q+1) (n+1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n+1) x) =
      (K.d p (p+1)).f (q+1) (totalSummandProjectionAt K p (q+1) n h x) +
        (-1 : ℤˣ)^(p+1) • ((K.X (p+1)).d q (q+1)
          (totalSummandProjectionAt K (p+1) q n (by omega) x)) := by
  have hd : (K.total (ComplexShape.up ℕ)).d n (n+1) ≫
      totalSummandProjectionAt K (p+1) (q+1) (n+1) (by omega) =
      totalSummandProjectionAt K p (q+1) n h ≫ (K.d p (p+1)).f (q+1) +
        (-1 : ℤˣ)^(p+1) •
          (totalSummandProjectionAt K (p+1) q n (by omega) ≫ (K.X (p+1)).d q (q+1)) := by
    change (K.D₁ _ n (n+1) + K.D₂ _ n (n+1)) ≫ _ = _
    rw [add_comp, horizontal_incoming, vertical_incoming]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
      using congrArg (fun f => f.hom x) hd

theorem differential_component_zero_column (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    totalSummandProjectionAt K 0 (n+1) (n+1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n+1) x) =
      (K.X 0).d n (n+1) (totalSummandProjectionAt K 0 n n (by omega) x) := by
  exact (congrArg (fun f => f.hom x) (zeroColumnTotalProjection_d K n)).symm

theorem differential_component_zero_row (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    totalSummandProjectionAt K (n+1) 0 (n+1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n+1) x) =
      (K.d n (n+1)).f 0 (totalSummandProjectionAt K n 0 n (by omega) x) := by
  have hd : (K.total (ComplexShape.up ℕ)).d n (n+1) ≫
      totalSummandProjectionAt K (n+1) 0 (n+1) (by omega) =
      totalSummandProjectionAt K n 0 n (by omega) ≫ (K.d n (n+1)).f 0 := by
    change (K.D₁ _ n (n+1) + K.D₂ _ n (n+1)) ≫ _ = _
    rw [add_comp, horizontal_incoming, vertical_incoming_zero, add_zero]
  exact congrArg (fun f => f.hom x) hd

end Sharpness.ElementaryCochainEdge
