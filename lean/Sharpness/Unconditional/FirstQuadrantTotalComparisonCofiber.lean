import Sharpness.Unconditional.FirstQuadrantTotalComparisonAcyclic
import Mathlib.Algebra.Homology.HomotopyCofiber

/-! The actual columnwise homotopy cofiber of a morphism of first-quadrant bicomplexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
variable {R : Type u} [CommRing R]

private theorem downNat_incoming (j : ℕ) : ∃ i, (ComplexShape.down ℕ).Rel i j := ⟨j+1, rfl⟩

variable {F G F' G' F'' G'' : ChainComplex (ModuleCat.{u} R) ℕ}

def chainCofiberSquareHomotopy (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : a ≫ g = f ≫ b) :
    Homotopy (f ≫ (b ≫ homotopyCofiber.inr g)) 0 :=
  (Homotopy.ofEq (by rw [← Category.assoc, ← w, Category.assoc])).trans
    (((homotopyCofiber.inrCompHomotopy g downNat_incoming).compLeft a).trans
      (Homotopy.ofEq (by simp)))

/-- The native homotopy cofiber map induced by a commuting square. -/
def chainCofiberMap (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : a ≫ g = f ≫ b) :
    homotopyCofiber f ⟶ homotopyCofiber g :=
  homotopyCofiber.desc f (b ≫ homotopyCofiber.inr g) (chainCofiberSquareHomotopy f g a b w)

@[reassoc]
theorem chainCofiberMap_inr (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : a ≫ g = f ≫ b) (n : ℕ) :
    homotopyCofiber.inrX f n ≫ (chainCofiberMap f g a b w).f n =
      b.f n ≫ homotopyCofiber.inrX g n := by
  exact homotopyCofiber.inrX_desc_f f _ _ n

@[reassoc]
theorem chainCofiberMap_inl (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : a ≫ g = f ≫ b) (n : ℕ) :
    homotopyCofiber.inlX f n (n+1) rfl ≫ (chainCofiberMap f g a b w).f (n+1) =
      a.f n ≫ homotopyCofiber.inlX g n (n+1) rfl := by
  rw [chainCofiberMap, homotopyCofiber.inlX_desc_f]
  simp [chainCofiberSquareHomotopy, Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft,
    homotopyCofiber.inrCompHomotopy_hom]

theorem chainCofiberMap_comp (f : F ⟶ G) (g : F' ⟶ G') (h : F'' ⟶ G'')
    (a : F ⟶ F') (b : G ⟶ G') (c : F' ⟶ F'') (d : G' ⟶ G'')
    (w : a ≫ g = f ≫ b) (w' : c ≫ h = g ≫ d) :
    chainCofiberMap f g a b w ≫ chainCofiberMap g h c d w' =
      chainCofiberMap f h (a ≫ c) (b ≫ d) (by
        rw [Category.assoc, w', ← Category.assoc, w, Category.assoc]) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      apply homotopyCofiber.ext_from_X' f 0 (by change ¬ _+1=0; omega)
      simp only [HomologicalComplex.comp_f, chainCofiberMap_inr_assoc,
        chainCofiberMap_inr, Category.assoc]
  | succ n =>
      apply homotopyCofiber.ext_from_X f n (n+1) rfl
      · simp only [HomologicalComplex.comp_f, chainCofiberMap_inl_assoc,
          chainCofiberMap_inl, Category.assoc]
      · simp only [HomologicalComplex.comp_f, chainCofiberMap_inr_assoc,
          chainCofiberMap_inr, Category.assoc]

theorem chainCofiberMap_zero (f : F ⟶ G) (g : F' ⟶ G')
    (w : (0 : F ⟶ F') ≫ g = f ≫ (0 : G ⟶ G')) :
    chainCofiberMap f g 0 0 w = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      apply homotopyCofiber.ext_from_X' f 0 (by change ¬ _+1=0; omega)
      simp only [chainCofiberMap_inr, HomologicalComplex.zero_f, zero_comp, comp_zero]
  | succ n =>
      apply homotopyCofiber.ext_from_X f n (n+1) rfl
      · simp only [chainCofiberMap_inl, HomologicalComplex.zero_f, zero_comp, comp_zero]
      · simp only [chainCofiberMap_inr, HomologicalComplex.zero_f, zero_comp, comp_zero]

theorem chainCofiberMap_eq_zero (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : a ≫ g = f ≫ b)
    (ha : a = 0) (hb : b = 0) : chainCofiberMap f g a b w = 0 := by
  subst a
  subst b
  exact chainCofiberMap_zero _ _ _

/-- Every vertical column is the native homotopy cofiber of the corresponding map. -/
def columnCofiber
    {K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ : K ⟶ L) :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  X p := homotopyCofiber (φ.f p)
  d p q := chainCofiberMap (φ.f p) (φ.f q) (K.d p q) (L.d p q) (φ.comm p q).symm
  shape p q hpq := by
    exact chainCofiberMap_eq_zero _ _ _ _ _ (K.shape p q hpq) (L.shape p q hpq)
  d_comp_d' p q r _ _ := by
    rw [chainCofiberMap_comp]
    exact chainCofiberMap_eq_zero _ _ _ _ _ (K.d_comp_d p q r) (L.d_comp_d p q r)

end Sharpness.TotalComparison
