import Sharpness.Unconditional.FirstQuadrantTotalComparisonCofiber

/-! Signed compatibility of totalization with the native homotopy cofiber. -/
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

private theorem cancel_add_pair {M : Type*} [AddCommGroup M] (a b c d : M)
    (h : a+c=0) : b+d=(a+b)+(c+d) := by
  calc
    b+d=0+(b+d) := (zero_add _).symm
    _=(a+c)+(b+d) := by rw [h]
    _=(a+b)+(c+d) := by abel

def columnCofiberInr : L ⟶ columnCofiber φ where
  f p := homotopyCofiber.inr (φ.f p)
  comm' p q _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact chainCofiberMap_inr (φ.f p) (φ.f q) (K.d p q) (L.d p q) _ n

def columnCofiberTotalLift (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) :=
  K.totalDesc (fun p q hpq => (-1 : ℤˣ)^p •
    (homotopyCofiber.inlX (φ.f p) q (q+1) rfl ≫
      (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p (q+1) (n+1)
        (by change p+(q+1)=n+1; change p+q=n at hpq; omega)))

@[reassoc]
theorem columnCofiberTotalLift_inclusion (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ columnCofiberTotalLift φ n =
      (-1 : ℤˣ)^p • (homotopyCofiber.inlX (φ.f p) q (q+1) rfl ≫
        (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p (q+1) (n+1)
          (by change p+(q+1)=n+1; omega)) := by
  exact HomologicalComplex₂.ι_totalDesc _ _ _ _ _

theorem columnCofiberTotalLift_horizontal (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega) ≫
        K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ columnCofiberTotalLift φ n +
      (show (K.X (p+1)).X q ⟶ ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      K.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega) ≫
        columnCofiberTotalLift φ (n+1) ≫
          (columnCofiber φ).D₁ (ComplexShape.down ℕ) (n+1+1) (n+1)) = 0 := by
  rw [← Category.assoc, chainTotal_horizontal_outgoing K p q n hpq,
    Category.assoc, columnCofiberTotalLift_inclusion,
    columnCofiberTotalLift_inclusion_assoc]
  rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    chainTotal_horizontal_outgoing (columnCofiber φ) p (q+1) (n+1) (by omega)]
  change (-1 : ℤˣ)^p • (_ ≫ _ ≫ _) +
    (-1 : ℤˣ)^(p+1) • (homotopyCofiber.inlX (φ.f (p+1)) q (q+1) rfl ≫
      (chainCofiberMap _ _ _ _ _).f (q+1) ≫ _) = 0
  rw [chainCofiberMap_inl_assoc, pow_succ, mul_smul]
  simp

theorem columnCofiberTotalLift_vertical (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) ≫
        K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ columnCofiberTotalLift φ n +
      (show (K.X p).X (q+1) ⟶ ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) ≫
        columnCofiberTotalLift φ (n+1) ≫
          (columnCofiber φ).D₂ (ComplexShape.down ℕ) (n+1+1) (n+1)) =
      (φ.f p).f (q+1) ≫ homotopyCofiber.inrX (φ.f p) (q+1) ≫
        (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p (q+1) (n+1)
          (by change p+(q+1)=n+1; omega) := by
  rw [← Category.assoc, chainTotal_vertical_outgoing K p q n hpq,
    Linear.units_smul_comp, Category.assoc, columnCofiberTotalLift_inclusion,
    Linear.comp_units_smul, smul_smul, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow, one_smul]
  rw [columnCofiberTotalLift_inclusion_assoc, Linear.units_smul_comp, Category.assoc,
    chainTotal_vertical_outgoing (columnCofiber φ) p (q+1) (n+1) (by omega),
    Linear.comp_units_smul, smul_smul, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow, one_smul]
  change _ + homotopyCofiber.inlX (φ.f p) (q+1) (q+1+1) rfl ≫
    homotopyCofiber.d (φ.f p) (q+1+1) (q+1) ≫ _ = _
  rw [homotopyCofiber.inlX_d_assoc (φ.f p) (q+1+1) (q+1) q rfl rfl]
  simp only [add_comp, neg_comp, Category.assoc]
  abel

theorem columnCofiberTotalLift_horizontal_all (p q n : ℕ) (hpq : p+q=n+1) :
    K.ιTotal (ComplexShape.down ℕ) p q (n+1) hpq ≫
        K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ columnCofiberTotalLift φ n +
      (show (K.X p).X q ⟶ ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      K.ιTotal (ComplexShape.down ℕ) p q (n+1) hpq ≫
        columnCofiberTotalLift φ (n+1) ≫
          (columnCofiber φ).D₁ (ComplexShape.down ℕ) (n+1+1) (n+1)) = 0 := by
  cases p with
  | succ p => exact columnCofiberTotalLift_horizontal φ p q n (by omega)
  | zero =>
      rw [← Category.assoc, chainTotal_horizontal_zero_outgoing K q n hpq,
        zero_comp, zero_add, columnCofiberTotalLift_inclusion_assoc,
        Linear.units_smul_comp, Category.assoc,
        chainTotal_horizontal_zero_outgoing (columnCofiber φ) (q+1) (n+1) (by omega)]
      simp

theorem columnCofiberTotalLift_vertical_all (p q n : ℕ) (hpq : p+q=n+1) :
    K.ιTotal (ComplexShape.down ℕ) p q (n+1) hpq ≫
        K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ columnCofiberTotalLift φ n +
      (show (K.X p).X q ⟶ ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      K.ιTotal (ComplexShape.down ℕ) p q (n+1) hpq ≫
        columnCofiberTotalLift φ (n+1) ≫
          (columnCofiber φ).D₂ (ComplexShape.down ℕ) (n+1+1) (n+1)) =
      (φ.f p).f q ≫ homotopyCofiber.inrX (φ.f p) q ≫
        (columnCofiber φ).ιTotal (ComplexShape.down ℕ) p q (n+1) hpq := by
  cases q with
  | succ q => exact columnCofiberTotalLift_vertical φ p q n (by omega)
  | zero =>
      rw [← Category.assoc, chainTotal_vertical_zero_outgoing K p n hpq,
        zero_comp, zero_add, columnCofiberTotalLift_inclusion_assoc,
        Linear.units_smul_comp, Category.assoc,
        chainTotal_vertical_outgoing (columnCofiber φ) p 0 (n+1) hpq,
        Linear.comp_units_smul, smul_smul, ← mul_pow]
      simp only [neg_mul_neg, one_mul, one_pow, one_smul]
      change homotopyCofiber.inlX (φ.f p) 0 1 rfl ≫
        homotopyCofiber.d (φ.f p) 1 0 ≫ _ = _
      rw [homotopyCofiber.inlX_d'_assoc (φ.f p) 1 0 rfl (by change ¬ _+1=0; omega)]

theorem columnCofiberTotalLift_comm_succ (n : ℕ) :
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)).f (n+1) ≫
        (HomologicalComplex₂.total.map (columnCofiberInr φ) (ComplexShape.down ℕ)).f (n+1) =
      (K.total (ComplexShape.down ℕ)).d (n+1) n ≫ columnCofiberTotalLift φ n +
        columnCofiberTotalLift φ (n+1) ≫
          ((columnCofiber φ).total (ComplexShape.down ℕ)).d (n+1+1) (n+1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=n+1 at hpq
  rw [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ιTotal_map]
  change (φ.f p).f q ≫ homotopyCofiber.inrX (φ.f p) q ≫ _ = _
  rw [← columnCofiberTotalLift_vertical_all φ p q n hpq]
  have hH := columnCofiberTotalLift_horizontal_all φ p q n hpq
  change _ = K.ιTotal (ComplexShape.down ℕ) p q (n+1) hpq ≫
    ((show (K.total (ComplexShape.down ℕ)).X (n+1) ⟶
      ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      (K.D₁ (ComplexShape.down ℕ) (n+1) n + K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫
        columnCofiberTotalLift φ n) +
      (show (K.total (ComplexShape.down ℕ)).X (n+1) ⟶
        ((columnCofiber φ).total (ComplexShape.down ℕ)).X (n+1) from
      columnCofiberTotalLift φ (n+1) ≫
        ((columnCofiber φ).D₁ (ComplexShape.down ℕ) (n+1+1) (n+1) +
          (columnCofiber φ).D₂ (ComplexShape.down ℕ) (n+1+1) (n+1))))
  simp only [comp_add, add_comp, Category.assoc]
  exact cancel_add_pair _ _ _ _ hH

theorem columnCofiberTotalLift_comm_zero :
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)).f 0 ≫
        (HomologicalComplex₂.total.map (columnCofiberInr φ) (ComplexShape.down ℕ)).f 0 =
      columnCofiberTotalLift φ 0 ≫
        ((columnCofiber φ).total (ComplexShape.down ℕ)).d 1 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=0 at hpq
  have hp : p=0 := by omega
  have hq : q=0 := by omega
  subst p
  subst q
  rw [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ιTotal_map,
    columnCofiberTotalLift_inclusion_assoc]
  change _ = ((-1 : ℤˣ)^0 • _) ≫
    ((columnCofiber φ).D₁ (ComplexShape.down ℕ) 1 0 +
      (columnCofiber φ).D₂ (ComplexShape.down ℕ) 1 0)
  simp only [pow_zero, one_smul, comp_add, Category.assoc]
  rw [chainTotal_horizontal_zero_outgoing (columnCofiber φ) 1 0 rfl,
    comp_zero, zero_add, chainTotal_vertical_outgoing (columnCofiber φ) 0 0 0 rfl]
  simp only [pow_zero, one_smul]
  change _ = homotopyCofiber.inlX (φ.f 0) 0 1 rfl ≫
    homotopyCofiber.d (φ.f 0) 1 0 ≫ _
  rw [homotopyCofiber.inlX_d'_assoc (φ.f 0) 1 0 rfl (by change ¬ _+1=0; omega)]
  rfl

def columnCofiberTotalHomotopy :
    Homotopy (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map (columnCofiberInr φ) (ComplexShape.down ℕ)) 0 where
  hom i j := if h : i+1=j then columnCofiberTotalLift φ i ≫
    eqToHom (congrArg (fun n => ((columnCofiber φ).total (ComplexShape.down ℕ)).X n) h) else 0
  zero i j h := by
    change ¬ i+1=j at h
    exact dif_neg h
  comm i := by
    rw [HomologicalComplex.zero_f, add_zero]
    cases i with
    | zero =>
        rw [dNext_eq_zero _ 0 (by change ¬ _+1=0; omega), zero_add,
          prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
        simp only [dite_true, eqToHom_refl, Category.comp_id, HomologicalComplex.comp_f]
        exact columnCofiberTotalLift_comm_zero φ
    | succ n =>
        rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
          prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+1+1) (n+1) from rfl)]
        simp only [dite_true, eqToHom_refl, Category.comp_id, HomologicalComplex.comp_f]
        exact columnCofiberTotalLift_comm_succ φ n

/-- The comparison uses the actual signed total differential and native cofiber. -/
def columnCofiberTotalComparison :
    homotopyCofiber (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) ⟶
      (columnCofiber φ).total (ComplexShape.down ℕ) :=
  homotopyCofiber.desc _
    (HomologicalComplex₂.total.map (columnCofiberInr φ) (ComplexShape.down ℕ))
    (columnCofiberTotalHomotopy φ)

@[reassoc]
theorem columnCofiberTotalComparison_inr (n : ℕ) :
    homotopyCofiber.inrX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n ≫
      (columnCofiberTotalComparison φ).f n =
      (HomologicalComplex₂.total.map (columnCofiberInr φ) (ComplexShape.down ℕ)).f n := by
  exact homotopyCofiber.inrX_desc_f _ _ _ _

@[reassoc]
theorem columnCofiberTotalComparison_inl (n : ℕ) :
    homotopyCofiber.inlX (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n (n+1) rfl ≫
      (columnCofiberTotalComparison φ).f (n+1) = columnCofiberTotalLift φ n := by
  rw [columnCofiberTotalComparison, homotopyCofiber.inlX_desc_f]
  simp [columnCofiberTotalHomotopy]

end Sharpness.TotalComparison


