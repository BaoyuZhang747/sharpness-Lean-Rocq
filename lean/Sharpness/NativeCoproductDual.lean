import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products

/-! Actual categorical coproduct duality. For an arbitrary family,
Hom out of its chosen coproduct is its product of Hom modules. For a
finite family the latter product is also the chosen coproduct. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {ι : Type v}
    (M : ι → ModuleCat.{max u v} R) (A : ModuleCat.{max u v} R)

def nativeCoproductHomEquiv : (∐ M ⟶ A) ≃ₗ[R] ∀ i, M i ⟶ A where
  toFun f i := Sigma.ι M i ≫ f
  invFun := Sigma.desc
  left_inv f := by
    apply Sigma.hom_ext
    intro i
    exact Sigma.ι_desc _ i
  right_inv f := funext (fun i => Sigma.ι_desc f i)
  map_add' f g := by
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r f := by
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def nativeCoproductDualEvaluation (i : ι) :
    ModuleCat.of R (∐ M ⟶ A) ⟶ ModuleCat.of R (M i ⟶ A) :=
  ModuleCat.ofHom ((LinearMap.proj i).comp (nativeCoproductHomEquiv M A).toLinearMap)

def nativeCoproductPiIso [Finite ι] : ∐ M ≅ ModuleCat.of R (∀ i, M i) := by
  classical
  letI := Fintype.ofFinite ι
  exact ModuleCat.coprodIsoDirectSum M ≪≫
    (DirectSum.linearEquivFunOnFintype R ι (fun i => M i)).toModuleIso

def nativeFiniteCoproductDualIso [Finite ι] :
    ∐ (fun i => ModuleCat.of R (M i ⟶ A)) ≅ ModuleCat.of R (∐ M ⟶ A) :=
  nativeCoproductPiIso (fun i => ModuleCat.of R (M i ⟶ A)) ≪≫
    (nativeCoproductHomEquiv M A).symm.toModuleIso

theorem nativeFiniteCoproductDualIso_inv_evaluation [Finite ι] (i : ι) :
    (nativeFiniteCoproductDualIso M A).inv ≫
      (nativeCoproductPiIso (fun i => ModuleCat.of R (M i ⟶ A))).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) = nativeCoproductDualEvaluation M A i := by
  simp only [nativeFiniteCoproductDualIso, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end Sharpness
