import Sharpness.DualNatBicomplex

/-! Both differentials of the actual dual bicomplex act by actual
precomposition. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

theorem dualNatBicomplex_horizontal_apply (p q : ℕ) (f : (K.X p).X q ⟶ A) :
    ((dualNatBicomplex K A).d p (p+1)).f q f = (K.d (p+1) p).f q ≫ f :=
  congrArg (fun a => a.f q f) (dualNatBicomplex_horizontal K A p)

theorem dualNatBicomplex_vertical_apply (p q : ℕ) (f : (K.X p).X q ⟶ A) :
    ((dualNatBicomplex K A).X p).d q (q+1) f = (K.X p).d (q+1) q ≫ f := rfl

end Sharpness
