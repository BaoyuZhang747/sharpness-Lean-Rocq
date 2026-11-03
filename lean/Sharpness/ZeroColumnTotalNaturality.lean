import Sharpness.ZeroColumnTotalMap

/-! The actual map to a total complex is natural under a commuting
map of augmented bicomplexes. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (φ : K ⟶ L) {A B : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1=0)
    (b : B ⟶ L.X 0) (hb : b ≫ L.d 0 1=0)
    (f : A ⟶ B) (h : f ≫ b=a ≫ φ.f 0)

set_option backward.isDefEq.respectTransparency false in
include h in
theorem zeroColumnTotalMap_naturality :
    f ≫ zeroColumnTotalMap L b hb =
      zeroColumnTotalMap K a ha ≫ HomologicalComplex₂.total.map φ (ComplexShape.up ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hc : f.f n ≫ b.f n = a.f n ≫ (φ.f 0).f n := HomologicalComplex.congr_hom h n
  have hi := HomologicalComplex₂.ιTotal_map K L φ (ComplexShape.up ℕ) 0 n n (by change 0+n=n; omega)
  change f.f n ≫ (b.f n ≫ L.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) =
    (a.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) ≫
      (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n
  calc
    _ = (f.f n ≫ b.f n) ≫ L.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := (Category.assoc _ _ _).symm
    _ = (a.f n ≫ (φ.f 0).f n) ≫ L.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) :=
      congrArg (fun t => t ≫ L.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) hc
    _ = a.f n ≫ (K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) ≫
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => a.f n ≫ t) hi.symm)
    _ = _ := (Category.assoc _ _ _).symm

end Sharpness
