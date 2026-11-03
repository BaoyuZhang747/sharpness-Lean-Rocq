import Sharpness.NativeCoproductDual
import Sharpness.SingularCochainFunctor

/-! Evaluation on the actual simplex generators identifies simplicial
cochains with functions. The formula for the coboundary and coefficient
naturality are consequences of the coproduct universal property. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable (R : Type u) [CommRing R] (X : SSet.{u}) (A : ModuleCat.{u} R)

def simplexCochainEquiv (n : ℕ) :
    ((X.chainComplex (ModuleCat.of R R)).X n ⟶ A) ≃ₗ[R]
      (X.obj (op ⦋n⦌) → A) :=
  (nativeCoproductHomEquiv (fun _ : X.obj (op ⦋n⦌) => ModuleCat.of R R) A).trans
    (LinearEquiv.piCongrRight (fun _ =>
      (ModuleCat.homLinearEquiv (R := R) (S := R)).trans
        (LinearMap.ringLmapEquivSelf R R A)))

theorem simplexCochainEquiv_apply (n : ℕ)
    (f : (X.chainComplex (ModuleCat.of R R)).X n ⟶ A) (x : X.obj (op ⦋n⦌)) :
    simplexCochainEquiv R X A n f x =
      f ((X.ιChainComplex (R := ModuleCat.of R R) x) (1 : R)) := rfl

theorem simplexCochainEquiv_coefficient {B : ModuleCat.{u} R} (a : A ⟶ B) (n : ℕ)
    (f : (X.chainComplex (ModuleCat.of R R)).X n ⟶ A) :
    simplexCochainEquiv R X B n (f ≫ a) =
      fun x => a (simplexCochainEquiv R X A n f x) := rfl

theorem simplexCochainEquiv_d (n : ℕ)
    (f : (X.chainComplex (ModuleCat.of R R)).X n ⟶ A)
    (x : X.obj (op ⦋n + 1⦌)) :
    simplexCochainEquiv R X A (n + 1)
        (((X.chainComplex (ModuleCat.of R R)).linearYonedaObj R A).d n (n + 1) f) x =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
        simplexCochainEquiv R X A n f (X.δ i x) := by
  change (X.ιChainComplex x ≫ (X.chainComplex (ModuleCat.of R R)).d (n+1) n ≫ f)
      (1 : R) = _
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

end Sharpness
