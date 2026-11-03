import Sharpness.Unconditional.FirstQuadrantTotalComparisonCone

/-! The degreewise inverse of the signed native total/cofiber comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
variable {R : Type u} [CommRing R]
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
variable (φ : K ⟶ L)

def columnCofiberTotalInverseSummand (n p : ℕ) : ∀ q : ℕ, p+q=n+1 →
    (((columnCofiber φ).X p).X q ⟶
      (homotopyCofiber (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ))).X (n+1))
  | 0, hpq => homotopyCofiber.sndX (φ.f p) 0 ≫
      L.ιTotal (ComplexShape.down ℕ) p 0 (n+1) hpq ≫
        homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) (n+1)
  | q+1, hpq => (-1 : ℤˣ)^p • (homotopyCofiber.fstX (φ.f p) (q+1) q rfl ≫
      K.ιTotal (ComplexShape.down ℕ) p q n (by change p+q=n; omega) ≫
        homotopyCofiber.inlX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n (n+1) rfl) +
      homotopyCofiber.sndX (φ.f p) (q+1) ≫
        L.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) hpq ≫
          homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) (n+1)

def columnCofiberTotalInverse : ∀ n : ℕ,
    ((columnCofiber φ).total (ComplexShape.down ℕ)).X n ⟶
      (homotopyCofiber (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ))).X n
  | 0 => (columnCofiber φ).totalDesc (fun p q hpq =>
      homotopyCofiber.sndX (φ.f p) q ≫
        L.ιTotal (ComplexShape.down ℕ) p q 0 hpq ≫
          homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) 0)
  | n+1 => (columnCofiber φ).totalDesc (fun p q hpq =>
      columnCofiberTotalInverseSummand φ n p q hpq)

@[reassoc]
theorem columnCofiberTotalInverse_inclusion_zero (p q : ℕ) (hpq : p+q=0) :
    (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p q 0 hpq ≫
        columnCofiberTotalInverse φ 0 =
      homotopyCofiber.sndX (φ.f p) q ≫ L.ιTotal (ComplexShape.down ℕ) p q 0 hpq ≫
        homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) 0 := by
  simp only [columnCofiberTotalInverse, HomologicalComplex₂.ι_totalDesc]

@[reassoc]
theorem columnCofiberTotalInverse_inclusion_bottom (p n : ℕ) (hp : p+0=n+1) :
    (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p 0 (n+1) hp ≫
        columnCofiberTotalInverse φ (n+1) =
      homotopyCofiber.sndX (φ.f p) 0 ≫ L.ιTotal (ComplexShape.down ℕ) p 0 (n+1) hp ≫
        homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) (n+1) := by
  simp only [columnCofiberTotalInverse, HomologicalComplex₂.ι_totalDesc,
    columnCofiberTotalInverseSummand]

@[reassoc]
theorem columnCofiberTotalInverse_inclusion_succ (p q n : ℕ) (hpq : p+(q+1)=n+1) :
    (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) hpq ≫
        columnCofiberTotalInverse φ (n+1) =
      (-1 : ℤˣ)^p • (homotopyCofiber.fstX (φ.f p) (q+1) q rfl ≫
        K.ιTotal (ComplexShape.down ℕ) p q n (by change p+q=n; omega) ≫
          homotopyCofiber.inlX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n (n+1) rfl) +
        homotopyCofiber.sndX (φ.f p) (q+1) ≫
          L.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) hpq ≫
            homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) (n+1) := by
  simp only [columnCofiberTotalInverse, HomologicalComplex₂.ι_totalDesc,
    columnCofiberTotalInverseSummand]

theorem columnCofiberTotalComparison_comp_inverse (n : ℕ) :
    (columnCofiberTotalComparison φ).f n ≫ columnCofiberTotalInverse φ n = 𝟙 _ := by
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) 0
      (by change ¬ _+1=0; omega)
    rw [columnCofiberTotalComparison_inr_assoc]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [HomologicalComplex₂.ιTotal_map_assoc, columnCofiberTotalInverse_inclusion_zero]
    change homotopyCofiber.inrX (φ.f p) q ≫ (homotopyCofiber.sndX (φ.f p) q ≫ _) = _
    simp only [homotopyCofiber.inrX_sndX_assoc]
    rfl
  | succ n =>
    apply homotopyCofiber.ext_from_X (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n (n+1) rfl
    · rw [columnCofiberTotalComparison_inl_assoc]
      apply HomologicalComplex₂.total.hom_ext
      intro p q hpq
      rw [columnCofiberTotalLift_inclusion_assoc, Linear.units_smul_comp,
        Category.assoc, columnCofiberTotalInverse_inclusion_succ]
      simp only [comp_add, Linear.comp_units_smul, homotopyCofiber.inlX_fstX_assoc,
        homotopyCofiber.inlX_sndX_assoc, add_zero, zero_comp,
        smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
      rfl
    · rw [columnCofiberTotalComparison_inr_assoc]
      apply HomologicalComplex₂.total.hom_ext
      intro p q hpq
      rw [HomologicalComplex₂.ιTotal_map_assoc]
      cases q with
      | zero =>
        rw [columnCofiberTotalInverse_inclusion_bottom]
        change homotopyCofiber.inrX (φ.f p) 0 ≫ (homotopyCofiber.sndX (φ.f p) 0 ≫ _) = _
        simp only [homotopyCofiber.inrX_sndX_assoc]
        rfl
      | succ q =>
        rw [columnCofiberTotalInverse_inclusion_succ]
        change homotopyCofiber.inrX (φ.f p) (q+1) ≫ _ = _
        simp only [comp_add, Linear.comp_units_smul, homotopyCofiber.inrX_fstX_assoc,
          homotopyCofiber.inrX_sndX_assoc, zero_comp, smul_zero, zero_add]
        rfl

theorem columnCofiberTotalInverse_comp_comparison (n : ℕ) :
    columnCofiberTotalInverse φ n ≫ (columnCofiberTotalComparison φ).f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  cases n with
  | zero =>
    have hq : q=0 := by change p+q=0 at hpq; omega
    subst q
    rw [columnCofiberTotalInverse_inclusion_zero_assoc,
      columnCofiberTotalComparison_inr, HomologicalComplex₂.ιTotal_map]
    change homotopyCofiber.sndX (φ.f p) 0 ≫ (homotopyCofiber.inrX (φ.f p) 0 ≫ _) = _
    rw [homotopyCofiber.sndX_inrX_assoc (φ.f p) 0 (by change ¬ _+1=0; omega)]
    simp only [Category.comp_id]
  | succ n =>
    cases q with
    | zero =>
      rw [columnCofiberTotalInverse_inclusion_bottom_assoc,
        columnCofiberTotalComparison_inr, HomologicalComplex₂.ιTotal_map]
      change homotopyCofiber.sndX (φ.f p) 0 ≫ (homotopyCofiber.inrX (φ.f p) 0 ≫ _) = _
      rw [homotopyCofiber.sndX_inrX_assoc (φ.f p) 0 (by change ¬ _+1=0; omega)]
      simp only [Category.comp_id]
    | succ q =>
      apply homotopyCofiber.ext_from_X (φ.f p) q (q+1) rfl
      · rw [columnCofiberTotalInverse_inclusion_succ_assoc]
        simp only [add_comp, Linear.units_smul_comp, Category.assoc,
          columnCofiberTotalComparison_inl, columnCofiberTotalComparison_inr,
          columnCofiberTotalLift_inclusion, HomologicalComplex₂.ιTotal_map]
        simp only [comp_add, Linear.comp_units_smul, homotopyCofiber.inlX_fstX_assoc,
          homotopyCofiber.inlX_sndX_assoc, zero_comp, add_zero, smul_smul,
          ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul, Category.comp_id]
      · rw [columnCofiberTotalInverse_inclusion_succ_assoc]
        simp only [add_comp, Linear.units_smul_comp, Category.assoc,
          columnCofiberTotalComparison_inl, columnCofiberTotalComparison_inr,
          columnCofiberTotalLift_inclusion, HomologicalComplex₂.ιTotal_map]
        simp only [comp_add, Linear.comp_units_smul, homotopyCofiber.inrX_fstX_assoc,
          homotopyCofiber.inrX_sndX_assoc, zero_comp, smul_zero, zero_add, Category.comp_id]
        rfl

instance columnCofiberTotalComparison_isIso : IsIso (columnCofiberTotalComparison φ) := by
  haveI : ∀ n, IsIso ((columnCofiberTotalComparison φ).f n) := fun n =>
    ⟨⟨columnCofiberTotalInverse φ n, columnCofiberTotalComparison_comp_inverse φ n,
      columnCofiberTotalInverse_comp_comparison φ n⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end Sharpness.TotalComparison
