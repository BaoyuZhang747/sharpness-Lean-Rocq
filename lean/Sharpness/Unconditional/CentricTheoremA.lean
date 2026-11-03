import Sharpness.Unconditional.CentricKanTransferNaturality
import Sharpness.Unconditional.CentricKanTransferComposite
import Sharpness.Unconditional.BurnsideTopAction
import Sharpness.Unconditional.PuigProducts
import Sharpness.CentricSimple

/-! Centric restricted-Mackey acyclicity by an actual acyclic right Kan
coefficient and its invertible pull-transfer composite. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat

/-- Once the actual top products are constructed, the centric Mackey
formula, prime-to-p marks, and derived Kan comparison prove acyclicity. -/
theorem restrictedCentric_acyclic_of_top_products
    (E : ∀ Q : F.CentricOrbit, ProductDecomposition F.centricTopObject Q)
    (M : RestrictedMackeyModule.{u,u,u} (PrimeLocalRing.{u} p)
      F.Orbit F.mackeyShape F.centricProperty) : Acyclic M.coefficient := by
  classical
  let R := PrimeLocalRing.{u} p
  let P := F.centricTopObject
  let α := overRanPullMap R P M.coefficient
  let β := F.overRanTransfer R M P E
  haveI : ∀ X, IsIso ((α ≫ β).app X) := by
    intro X
    change IsIso ((overRanPullMap R P M.coefficient).app (op X.unop) ≫
      F.overRanTransferApp R M P (E X.unop))
    rw [F.overRanPullMap_comp_transferApp R M P]
    exact F.topProductPushPull_isIso p hS sat M (E X.unop).swap
  letI : IsIso (α ≫ β) := NatIso.isIso_of_isIso_app _
  exact Burnside.acyclic_of_invertible_acyclic_factorization R
    (overRan_acyclic_of_productDecomposition R P E ((Over.forget P).op ⋙ M.coefficient)) α β

/-- Every restricted centric Mackey coefficient over the localized integers
is acyclic. The product family is constructed from the saturation axioms. -/
theorem restrictedCentric_acyclic
    (M : RestrictedMackeyModule.{u,u,u} (PrimeLocalRing.{u} p)
      F.Orbit F.mackeyShape F.centricProperty) : Acyclic M.coefficient :=
  F.restrictedCentric_acyclic_of_top_products p hS sat
    (F.centricProductDecomposition p hS sat F.centricTopObject) M

/-- The former published Theorem A input, now constructed without any
reference-result premise. -/
def provedDiazParkTheoremAInput : F.DiazParkTheoremAInput p hS sat where
  theorem_A := F.restrictedCentric_acyclic p hS sat

end Sharpness.FusionSystem
