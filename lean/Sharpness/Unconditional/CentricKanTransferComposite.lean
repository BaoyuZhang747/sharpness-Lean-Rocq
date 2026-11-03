import Sharpness.Unconditional.CentricKanTransfer

/-! The composite of the canonical Kan pull and the sum-push transfer
is exactly the sum of the actual transfer/restriction operators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (R : Type u) [CommRing R]
    (M : RestrictedMackeyModule.{u,u,u} R F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup))
    (P : F.CentricOrbit)

theorem overRanPullMap_comp_evaluation {X Q : F.CentricOrbit}
    (a : X ⟶ P) (b : X ⟶ Q) :
    (overRanPullMap R P M.coefficient).app (op Q) ≫
      overRanEvaluation R P M.coefficient a b = ModuleCat.ofHom (M.pull b) := by
  let η := ((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M.coefficient
  have hn := η.naturality b.op
  change M.coefficient.map b.op ≫ η.app (op X) =
    η.app (op Q) ≫ (overRanCoefficient R P M.coefficient).map b.op at hn
  change η.app (op Q) ≫ ((overRanCoefficient R P M.coefficient).map b.op ≫ _) = _
  rw [← Category.assoc, ← hn, Category.assoc]
  have ht := CategoryTheory.Functor.ranCounit_app_app_ranAdjunction_unit_app_app
    (Over.forget P).op M.coefficient (op (Over.mk a))
  change η.app (op X) ≫ _ = 𝟙 (M.coefficient.obj (op X)) at ht
  rw [ht]
  exact Category.comp_id _

/-- The transfer composite is the finite sum used by the Burnside action. -/
theorem overRanPullMap_comp_transferApp {Q : F.CentricOrbit}
    (E : ProductDecomposition P Q) :
    (overRanPullMap R P M.coefficient).app (op Q) ≫ F.overRanTransferApp R M P E =
      letI := Fintype.ofFinite E.Index
      ModuleCat.ofHom (∑ i : E.Index, (M.push (E.right i)).comp (M.pull (E.right i))) := by
  classical
  letI := Fintype.ofFinite E.Index
  unfold overRanTransferApp
  rw [Preadditive.comp_sum]
  have he : (∑ i : E.Index, (overRanPullMap R P M.coefficient).app (op Q) ≫
      (overRanEvaluation R P M.coefficient (E.left i) (E.right i) ≫
        ModuleCat.ofHom (M.push (E.right i)))) =
      ∑ i : E.Index, ModuleCat.ofHom (M.pull (E.right i)) ≫ ModuleCat.ofHom (M.push (E.right i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Category.assoc, F.overRanPullMap_comp_evaluation R M P]
  rw [he]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom]

end Sharpness.FusionSystem
