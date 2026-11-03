import Sharpness.BiprodCokernelImageQuotient
import Mathlib.Algebra.Homology.SpectralObject.Page

/-! The page object E(f1,f2,f3) is the quotient of the image from
H(f1 f2) to H(f1 f2 f3) by the image from H(f1). This follows from
the actual native spectral-object exact sequences and the proved
linear image-quotient lemma. It is not a convergence assumption. -/
set_option autoImplicit false
noncomputable section
universe u v t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
variable {R : Type u} [CommRing R] {ι : Type t} [Category.{v} ι]
    (X : Abelian.SpectralObject (ModuleCat.{u} R) ι)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (n : ℤ)

def spectralImageLeft : (X.H n).obj (mk₁ f₁) ⟶ (X.H n).obj (mk₁ (f₁ ≫ f₂)) :=
  (X.H n).map (twoδ₂Toδ₁ f₁ f₂ (f₁ ≫ f₂) rfl)

def spectralImageRight : (X.H n).obj (mk₁ (f₁ ≫ f₂)) ⟶
    (X.H n).obj (mk₁ ((f₁ ≫ f₂) ≫ f₃)) :=
  (X.H n).map (twoδ₂Toδ₁ (f₁ ≫ f₂) f₃ ((f₁ ≫ f₂) ≫ f₃) rfl)

set_option backward.isDefEq.respectTransparency false in
def spectralObjectImageQuotientIso : X.E f₁ f₂ f₃ (n-1) n (n+1) ≅
    ModuleCat.of R (ImageQuotient (spectralImageLeft X f₁ f₂ n).hom
      (spectralImageRight X f₁ f₂ f₃ n).hom) := by
  let S := X.cokernelSequenceE f₁ f₂ f₃ (f₁ ≫ f₂) rfl (n-1) n (n+1)
  let v := spectralImageRight X f₁ f₂ f₃ n
  letI : Epi S.g := inferInstanceAs
    (Epi (X.cokernelSequenceE f₁ f₂ f₃ (f₁ ≫ f₂) rfl (n-1) n (n+1)).g)
  have he : LinearMap.range (X.δ (f₁ ≫ f₂) f₃ (n-1) n).hom = LinearMap.ker v.hom :=
    (X.exact₁ (f₁ ≫ f₂) f₃ ((f₁ ≫ f₂) ≫ f₃) rfl (n-1) n).moduleCat_range_eq_ker
  exact biprodCokernelImageQuotientIso (spectralImageLeft X f₁ f₂ n)
    (X.δ (f₁ ≫ f₂) f₃ (n-1) n) S.g v S.zero
    (X.cokernelSequenceE_exact f₁ f₂ f₃ (f₁ ≫ f₂) rfl (n-1) n (n+1)) he

end Sharpness
