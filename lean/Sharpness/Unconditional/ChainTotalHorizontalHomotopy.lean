import Sharpness.Unconditional.ChainTotalIncomingProjections
import Mathlib.Algebra.Homology.Homotopy

/-! Totalization of actual horizontal homotopies of first-quadrant bicomplexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
variable {R : Type u} [CommRing R]
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
variable {f g : K ⟶ L} (h : Homotopy f g)

def chainTotalHorizontalHom (n m : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (L.total (ComplexShape.down ℕ)).X m :=
  K.totalDesc fun p q _ => (h.hom p (p+1)).f q ≫
    L.ιTotalOrZero (ComplexShape.down ℕ) (p+1) q m

@[reassoc]
theorem chainTotalHorizontalHom_inclusion (p q n m : ℕ) (hpq : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ chainTotalHorizontalHom h n m =
      (h.hom p (p+1)).f q ≫ L.ιTotalOrZero (ComplexShape.down ℕ) (p+1) q m := by
  simp only [chainTotalHorizontalHom, HomologicalComplex₂.ι_totalDesc]

@[reassoc]
theorem chainTotalHorizontalHom_inclusion_succ (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ chainTotalHorizontalHom h n (n+1) =
      (h.hom p (p+1)).f q ≫
        L.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega) := by
  rw [chainTotalHorizontalHom_inclusion, HomologicalComplex₂.ιTotalOrZero_eq]

theorem chainTotalHorizontalHom_zero (n m : ℕ) (hnm : ¬(ComplexShape.down ℕ).Rel m n) :
    chainTotalHorizontalHom h n m = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=n at hpq
  rw [chainTotalHorizontalHom_inclusion, HomologicalComplex₂.ιTotalOrZero_eq_zero,
    comp_zero, comp_zero]
  change p+1+q ≠ m
  change ¬n+1=m at hnm
  omega

theorem chainTotalHorizontalHom_vertical_cancel (p q n : ℕ) (hpq : p+q=n) :
    (K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) ≫
        K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫ chainTotalHorizontalHom h n (n+1) +
      (K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) ≫
        chainTotalHorizontalHom h (n+1) (n+2)) ≫
        (show (L.total (ComplexShape.down ℕ)).X (n+2) ⟶ (L.total (ComplexShape.down ℕ)).X (n+1) from
          L.D₂ (ComplexShape.down ℕ) (n+2) (n+1)) = 0 := by
  rw [chainTotal_vertical_outgoing K p q n hpq, Linear.units_smul_comp,
    Category.assoc, chainTotalHorizontalHom_inclusion_succ,
    chainTotalHorizontalHom_inclusion_succ, Category.assoc,
    chainTotal_vertical_outgoing L (p+1) q (n+1) (by omega), Linear.comp_units_smul,
    (h.hom p (p+1)).comm_assoc (q+1) q]
  rw [pow_succ, mul_smul, Units.neg_smul, one_smul, smul_neg]
  abel


theorem chainTotalHorizontalHom_horizontal_comm_succ (n : ℕ) :
    (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f (n+1) =
      (show (K.total (ComplexShape.down ℕ)).X (n+1) ⟶ (K.total (ComplexShape.down ℕ)).X n from
        K.D₁ (ComplexShape.down ℕ) (n+1) n) ≫ chainTotalHorizontalHom h n (n+1) +
      chainTotalHorizontalHom h (n+1) (n+2) ≫
        (show (L.total (ComplexShape.down ℕ)).X (n+2) ⟶ (L.total (ComplexShape.down ℕ)).X (n+1) from
          L.D₁ (ComplexShape.down ℕ) (n+2) (n+1)) +
      (HomologicalComplex₂.total.map g (ComplexShape.down ℕ)).f (n+1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=n+1 at hpq
  simp only [comp_add, HomologicalComplex₂.ιTotal_map]
  rw [chainTotalHorizontalHom_inclusion_succ_assoc,
    chainTotal_horizontal_outgoing L p q (n+1) hpq]
  cases p with
  | zero =>
      rw [← Category.assoc (K.ιTotal _ 0 q (n+1) hpq) (K.D₁ _ (n+1) n)
        (chainTotalHorizontalHom h n (n+1)),
        chainTotal_horizontal_zero_outgoing K q n hpq, zero_comp, zero_add]
      have hc := congrArg (fun a => a.f q) (h.comm 0)
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        zero_add, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hc
      rw [hc, add_comp, Category.assoc]
  | succ p =>
      rw [← Category.assoc (K.ιTotal _ (p+1) q (n+1) hpq) (K.D₁ _ (n+1) n)
        (chainTotalHorizontalHom h n (n+1)),
        chainTotal_horizontal_outgoing K p q n (by omega), Category.assoc,
        chainTotalHorizontalHom_inclusion_succ]
      have hc := congrArg (fun a => a.f q) (h.comm (p+1))
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hc
      rw [hc]
      simp only [add_comp, Category.assoc]


theorem chainTotalHorizontalHom_vertical_cancel_succ (n : ℕ) :
    (show (K.total (ComplexShape.down ℕ)).X (n+1) ⟶ (K.total (ComplexShape.down ℕ)).X n from
      K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫ chainTotalHorizontalHom h n (n+1) +
      chainTotalHorizontalHom h (n+1) (n+2) ≫
        (show (L.total (ComplexShape.down ℕ)).X (n+2) ⟶ (L.total (ComplexShape.down ℕ)).X (n+1) from
          L.D₂ (ComplexShape.down ℕ) (n+2) (n+1)) = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=n+1 at hpq
  simp only [comp_add, comp_zero]
  cases q with
  | zero =>
      rw [← Category.assoc (K.ιTotal _ p 0 (n+1) hpq) (K.D₂ _ (n+1) n)
        (chainTotalHorizontalHom h n (n+1)),
        chainTotal_vertical_zero_outgoing K p n hpq, zero_comp,
        chainTotalHorizontalHom_inclusion_succ_assoc,
        chainTotal_vertical_zero_outgoing L (p+1) (n+1) (by omega), comp_zero, add_zero]
  | succ q =>
      simpa only [Category.assoc] using chainTotalHorizontalHom_vertical_cancel h p q n (by omega)

theorem chainTotalHorizontalHom_comm_zero :
    (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f 0 =
      chainTotalHorizontalHom h 0 1 ≫ (L.total (ComplexShape.down ℕ)).d 1 0 +
      (HomologicalComplex₂.total.map g (ComplexShape.down ℕ)).f 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=0 at hpq
  obtain rfl : p=0 := by omega
  obtain rfl : q=0 := by omega
  simp only [comp_add, HomologicalComplex₂.ιTotal_map,
    chainTotalHorizontalHom_inclusion_succ_assoc, HomologicalComplex₂.total_d]
  rw [chainTotal_horizontal_outgoing L 0 0 0 rfl,
    chainTotal_vertical_zero_outgoing L 1 0 rfl, comp_zero, add_zero]
  have hc := congrArg (fun a => a.f 0) (h.comm 0)
  simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
    zero_add, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hc
  rw [hc, add_comp, Category.assoc]

theorem chainTotalHorizontalHom_comm_succ (n : ℕ) :
    (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f (n+1) =
      (K.total (ComplexShape.down ℕ)).d (n+1) n ≫ chainTotalHorizontalHom h n (n+1) +
      chainTotalHorizontalHom h (n+1) (n+2) ≫ (L.total (ComplexShape.down ℕ)).d (n+2) (n+1) +
      (HomologicalComplex₂.total.map g (ComplexShape.down ℕ)).f (n+1) := by
  rw [HomologicalComplex₂.total_d, HomologicalComplex₂.total_d, add_comp, comp_add]
  rw [chainTotalHorizontalHom_horizontal_comm_succ h n]
  have hv := chainTotalHorizontalHom_vertical_cancel_succ h n
  have hv' := eq_neg_of_add_eq_zero_left hv
  rw [hv']
  abel

/-- Native totalization sends every genuine horizontal bicomplex homotopy
 to a genuine chain homotopy, including the zero-degree boundary. -/
def chainTotalHorizontalHomotopy :
    Homotopy (HomologicalComplex₂.total.map f (ComplexShape.down ℕ))
      (HomologicalComplex₂.total.map g (ComplexShape.down ℕ)) where
  hom := chainTotalHorizontalHom h
  zero := chainTotalHorizontalHom_zero h
  comm n := by
    cases n with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add]
        exact chainTotalHorizontalHom_comm_zero h
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        exact chainTotalHorizontalHom_comm_succ h n

def chainTotalHorizontalHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total (ComplexShape.down ℕ)) (L.total (ComplexShape.down ℕ)) where
  hom := HomologicalComplex₂.total.map e.hom (ComplexShape.down ℕ)
  inv := HomologicalComplex₂.total.map e.inv (ComplexShape.down ℕ)
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex₂.total.map_comp _ _ _).symm).trans
    ((chainTotalHorizontalHomotopy e.homotopyHomInvId).trans
      (Homotopy.ofEq (HomologicalComplex₂.total.map_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex₂.total.map_comp _ _ _).symm).trans
    ((chainTotalHorizontalHomotopy e.homotopyInvHomId).trans
      (Homotopy.ofEq (HomologicalComplex₂.total.map_id _ _)))

end Sharpness
