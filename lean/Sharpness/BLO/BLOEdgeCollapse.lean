import Sharpness.BLO.BLOEdgeNative

/-! Elementary all-degree comparison for the actual BLO replacement.
The two explicit algebraic premises are discharged in the final sharpness
module by the canonical comparison and the new E3 companion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]

theorem BLOEdgeReplacementEdge_isIso_of_positive
    (hpos : ∀ n s : ℕ, 0 < s → IsZero (covariantHigherLimit (PrimeField.{u} p)
      (L.BLOCohomologyDiagram p n) s)) (n : ℕ) :
    IsIso (L.BLOEdgeReplacementEdge p n) := by
  have h : ∀ q s : ℕ, IsZero (higherLimit
      (L.BLOEdgeReplacementCohomologyDiagram p q) (s + 1)) := by
    intro q s
    exact IsZero.of_iso (hpos q (s + 1) (Nat.zero_lt_succ s))
      (L.BLOEdgeReplacementHigherLimitIso p q (s + 1))
  letI := elementaryReplacementLimitEdge_isIso (L.BLOEdgeCochainDiagram p) h n
  unfold BLOEdgeReplacementEdge
  infer_instance

theorem BLOEdgeCochainAugmentation_quasiIso_of_positive_restriction
    (hpos : ∀ n s : ℕ, 0 < s → IsZero (covariantHigherLimit (PrimeField.{u} p)
      (L.BLOCohomologyDiagram p n) s))
    (hres : ∀ n : ℕ, IsIso (L.BLOEdgeRestrictionToLimit p n)) :
    QuasiIso (L.BLOEdgeCochainAugmentation p) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  letI := L.BLOEdgeReplacementEdge_isIso_of_positive p hpos n
  apply (isIso_comp_right_iff
    (HomologicalComplex.homologyMap (L.BLOEdgeCochainAugmentation p) n)
    (L.BLOEdgeReplacementEdge p n)).mp
  rw [← L.BLOEdgeRestrictionToLimit_eq_edge p n]
  exact hres n

end Sharpness.FusionSystem.CentricLinkingSystem
