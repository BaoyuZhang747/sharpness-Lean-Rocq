import Sharpness.ProductCochains

/-! Actual maps into and projections from the product cochain complex,
with their degreewise and composite formulas. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] {ι : Type u}
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)

def productCochainsLift {A : CochainComplex (ModuleCat.{u} R) ℕ} (a : ∀ i, A ⟶ K i) :
    A ⟶ productCochains K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.pi (fun i => (a i).f n |>.hom))) (by
    intro n
    simp only [productCochains, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun t => t x) ((a i).comm n (n+1)))

def productCochainsProjection (i : ι) : productCochains K ⟶ K i :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.proj i)) (by
    intro n
    simp only [productCochains, CochainComplex.of_d]
    rfl)

theorem productCochainsLift_projection {A : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : ∀ i, A ⟶ K i) (i : ι) : productCochainsLift K a ≫ productCochainsProjection K i = a i := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end Sharpness
