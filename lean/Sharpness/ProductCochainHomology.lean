import Sharpness.ProductCochains
import Sharpness.ShortComplexPiHomology

/-! Native cohomology of the actual product cochain complex is the
actual product of native cohomology modules, for an arbitrary indexing
type. This supplies the concrete vertical terms of the subgroup model. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι : Type u} [CommRing R]
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)

theorem productCochains_d_apply (i j : ℕ) (x : (productCochains K).X i) (k : ι) :
    (productCochains K).d i j x k = (K k).d i j (x k) := by
  by_cases h : i+1 = j
  · subst j
    simp only [productCochains, CochainComplex.of_d]
    rfl
  · rw [(productCochains K).shape i j h, (K k).shape i j h]
    rfl

set_option backward.isDefEq.respectTransparency false in
def productCochainsShortComplexIso (n : ℕ) :
    (productCochains K).sc n ≅ piShortComplex (fun i => (K i).sc n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      exact (productCochains_d_apply K ((ComplexShape.up ℕ).prev n) n x i).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      exact (productCochains_d_apply K n ((ComplexShape.up ℕ).next n) x i).symm)

def productCochainsHomologyIso (n : ℕ) :
    (productCochains K).homology n ≅ ModuleCat.of R (∀ i, (K i).homology n) :=
  ShortComplex.homologyMapIso (productCochainsShortComplexIso K n) ≪≫
    piShortComplexHomologyIso (fun i => (K i).sc n)

end Sharpness
