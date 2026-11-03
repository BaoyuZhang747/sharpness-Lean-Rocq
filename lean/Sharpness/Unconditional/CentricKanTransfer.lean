import Sharpness.Unconditional.CentricKanTransferCoordinates
import Sharpness.Unconditional.CentricKanTransferProduct
import Sharpness.Unconditional.ProductDecompositionUniqueness
import Sharpness.Unconditional.BurnsideMackeyAction

/-! The covariant transfer out of the acyclic slice right Kan coefficient.
Naturality follows from the actual centric Mackey pullback decomposition. -/
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

def overRanTransferApp {Q : F.CentricOrbit} (D : ProductDecomposition P Q) :
    (overRanCoefficient R P M.coefficient).obj (op Q) ⟶ M.coefficient.obj (op Q) := by
  classical
  letI := Fintype.ofFinite D.Index
  exact ∑ i, overRanEvaluation R P M.coefficient (D.left i) (D.right i) ≫
    ModuleCat.ofHom (M.push (D.right i))

theorem overRanTransferTerm_iso {X Y Q : F.CentricOrbit}
    (a : X ⟶ P) (b : X ⟶ Q) (a' : Y ⟶ P) (b' : Y ⟶ Q)
    (e : X ≅ Y) (ha : e.hom ≫ a' = a) (hb : e.hom ≫ b' = b) :
    overRanEvaluation R P M.coefficient a b ≫ ModuleCat.ofHom (M.push b) =
      overRanEvaluation R P M.coefficient a' b' ≫ ModuleCat.ofHom (M.push b') := by
  subst a b
  rw [overRanEvaluation_precomp, M.push_comp]
  change (_ ≫ ModuleCat.ofHom (M.pull e.hom)) ≫
    (ModuleCat.ofHom (M.push e.hom) ≫ ModuleCat.ofHom (M.push b')) = _
  rw [Category.assoc, ← Category.assoc (ModuleCat.ofHom (M.pull e.hom))]
  have he : ModuleCat.ofHom (M.pull e.hom) ≫ ModuleCat.ofHom (M.push e.hom) =
      𝟙 (M.coefficient.obj (op Y)) := by
    apply ModuleCat.hom_ext
    exact M.push_pull_iso e
  rw [he]
  rfl

/-- Sum-push transfer is independent of the chosen representing summands. -/
theorem overRanTransferApp_eq {Q : F.CentricOrbit} (D E : ProductDecomposition P Q) :
    F.overRanTransferApp R M P D = F.overRanTransferApp R M P E := by
  classical
  letI := Fintype.ofFinite D.Index
  letI := Fintype.ofFinite E.Index
  unfold overRanTransferApp
  apply Fintype.sum_equiv (D.indexEquiv E)
  intro i
  exact F.overRanTransferTerm_iso R M P _ _ _ _ (D.apexIso E i)
    (D.apexIso_hom_left E i) (D.apexIso_hom_right E i)

end Sharpness.FusionSystem
