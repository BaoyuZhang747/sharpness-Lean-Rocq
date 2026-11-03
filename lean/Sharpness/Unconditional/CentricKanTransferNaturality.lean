import Sharpness.Unconditional.CentricKanTransfer

/-! The actual Mackey formula proves naturality of the sum-push transfer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

private theorem sum_sigma_any_fintype {I : Type u} [Fintype I] {J : I → Type u}
    [∀ i, Fintype (J i)] [h : Fintype (Σ i, J i)] {A : Type u} [AddCommMonoid A]
    (g : (Σ i, J i) → A) : ∑ z, g z = ∑ i, ∑ j, g ⟨i, j⟩ := by
  have he : h = Sigma.instFintype := Subsingleton.elim _ _
  cases he
  exact Fintype.sum_sigma g

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (R : Type u) [CommRing R]
    (M : RestrictedMackeyModule.{u,u,u} R F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup))
    (P : F.CentricOrbit)

theorem overRanEvaluation_pulledProduct {Q Q' : F.CentricOrbit}
    (D : ProductDecomposition P Q) (f : Q' ⟶ Q) (i : D.Index)
    (j : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f (D.right i)) :
    (overRanCoefficient R P M.coefficient).map f.op ≫
        overRanEvaluation R P M.coefficient
          ((restrictedSpan F.mackeyShape _ f (D.right i) j).right ≫ D.left i)
          (restrictedSpan F.mackeyShape _ f (D.right i) j).left =
      overRanEvaluation R P M.coefficient (D.left i) (D.right i) ≫
        ModuleCat.ofHom (M.pull (restrictedSpan F.mackeyShape _ f (D.right i) j).right) := by
  rw [overRanEvaluation_postcomp, F.restrictedCentricSpan_comm,
    overRanEvaluation_precomp]
  rfl

theorem mackey_categorical {A B T : F.CentricOrbit} (f : A ⟶ T) (g : B ⟶ T) :
    ModuleCat.ofHom (M.push g) ≫ ModuleCat.ofHom (M.pull f) =
      ∑ j : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
        ModuleCat.ofHom (M.pull (restrictedSpan F.mackeyShape _ f g j).right) ≫
          ModuleCat.ofHom (M.push (restrictedSpan F.mackeyShape _ f g j).left) := by
  apply ModuleCat.hom_ext
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_sum] using M.mackey f g

/-- The sum-push formula after base change is exactly the restricted Mackey
formula on every original product summand. -/
theorem overRanTransferApp_basechange {Q Q' : F.CentricOrbit}
    (D : ProductDecomposition P Q) (f : Q' ⟶ Q) :
    (overRanCoefficient R P M.coefficient).map f.op ≫
        F.overRanTransferApp R M P (F.pulledProductDecomposition D f) =
      F.overRanTransferApp R M P D ≫ M.coefficient.map f.op := by
  classical
  letI := Fintype.ofFinite D.Index
  letI pulledFintype : Fintype (F.PulledProductIndex D f) := Fintype.ofFinite _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [overRanTransferApp, ModuleCat.hom_comp, ModuleCat.hom_sum,
    LinearMap.comp_apply, LinearMap.sum_apply, ModuleCat.hom_ofHom]
  change (∑ z : F.PulledProductIndex D f,
      M.push (F.pulledProductSpan D f z).left
        ((overRanEvaluation R P M.coefficient
          ((F.pulledProductSpan D f z).right ≫ D.left z.1)
          (F.pulledProductSpan D f z).left).hom
          (((overRanCoefficient R P M.coefficient).map f.op).hom x))) =
      M.pull f (∑ i : D.Index, M.push (D.right i)
        ((overRanEvaluation R P M.coefficient (D.left i) (D.right i)).hom x))
  rw [sum_sigma_any_fintype, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hm := LinearMap.congr_fun (M.mackey f (D.right i))
    ((overRanEvaluation R P M.coefficient (D.left i) (D.right i)).hom x)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (M.push (restrictedSpan F.mackeyShape _ f (D.right i) j).left)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (F.overRanEvaluation_pulledProduct R M P D f i j)) x

/-- Transfer is natural for any choice of the representable products. -/
theorem overRanTransferApp_naturality
    (E : ∀ Q : F.CentricOrbit, ProductDecomposition P Q)
    {Q Q' : F.CentricOrbit} (f : Q' ⟶ Q) :
    (overRanCoefficient R P M.coefficient).map f.op ≫
        F.overRanTransferApp R M P (E Q') =
      F.overRanTransferApp R M P (E Q) ≫ M.coefficient.map f.op := by
  rw [← F.overRanTransferApp_eq R M P (F.pulledProductDecomposition (E Q) f) (E Q')]
  exact F.overRanTransferApp_basechange R M P (E Q) f

/-- The covariant transfer from the actual acyclic right Kan coefficient. -/
def overRanTransfer (E : ∀ Q : F.CentricOrbit, ProductDecomposition P Q) :
    overRanCoefficient R P M.coefficient ⟶ M.coefficient where
  app Q := F.overRanTransferApp R M P (E Q.unop)
  naturality {Q Q'} f := F.overRanTransferApp_naturality R M P E f.unop

end Sharpness.FusionSystem
