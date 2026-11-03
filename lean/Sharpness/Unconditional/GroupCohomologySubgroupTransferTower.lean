import Sharpness.Unconditional.GroupCohomologyHomTransferTower
import Sharpness.Unconditional.GroupCohomologyCosetTransport

/-! Transitivity on the actual subgroup Hom and cochain interfaces, with all
three subgroups in a fixed ambient group. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
open scoped BigOperators

variable {R G : Type u} [CommRing R] [Group G]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Actual subgroup transfer is transitive, before passing to cohomology. -/
theorem subgroupHomTransfer_comp (P Q T : Subgroup G) (hPQ : P ≤ Q) (hQT : Q ≤ T)
    [(P.subgroupOf T).FiniteIndex] [(Q.subgroupOf T).FiniteIndex]
    [(P.subgroupOf Q).FiniteIndex] (X V : Rep.{u} R G)
    (f : Rep.res P.subtype X ⟶ Rep.res P.subtype V) :
    subgroupHomTransfer Q T hQT X V (subgroupHomTransfer P Q hPQ X V f) =
      subgroupHomTransfer P T (hPQ.trans hQT) X V f := by
  apply Rep.hom_ext
  ext x
  change (subgroupHomTransfer Q T hQT X V (subgroupHomTransfer P Q hPQ X V f)).hom x =
    (subgroupHomTransfer P T (hPQ.trans hQT) X V f).hom x
  rw [subgroupHomTransfer_apply, subgroupHomTransfer_apply]
  rw [subgroupRightCosetTower_sum P Q T hPQ hQT
    (fun t : T => V.ρ (t : G)⁻¹ (f.hom (X.ρ (t : G) x)))
    (fun p t => homTransfer_summand_invariant P X V f x ⟨(p.val : G), p.property⟩ t)]
  apply Finset.sum_congr rfl
  intro a _
  rw [subgroupHomTransfer_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Subgroup.coe_mul, mul_inv_rev, map_mul, Module.End.mul_apply]

/-- Linear-map form of subgroup transfer transitivity. -/
theorem subgroupHomTransfer_comp_linear (P Q T : Subgroup G)
    (hPQ : P ≤ Q) (hQT : Q ≤ T)
    [(P.subgroupOf T).FiniteIndex] [(Q.subgroupOf T).FiniteIndex]
    [(P.subgroupOf Q).FiniteIndex] (X V : Rep.{u} R G) :
    (subgroupHomTransfer Q T hQT X V).comp (subgroupHomTransfer P Q hPQ X V) =
      subgroupHomTransfer P T (hPQ.trans hQT) X V := by
  apply LinearMap.ext
  intro f
  exact subgroupHomTransfer_comp P Q T hPQ hQT X V f

/-- Transfers compose on the Hom cochain complex of any ambient chain complex. -/
theorem subgroupHomComplexTransfer_comp (P Q T : Subgroup G)
    (hPQ : P ≤ Q) (hQT : Q ≤ T)
    [(P.subgroupOf T).FiniteIndex] [(Q.subgroupOf T).FiniteIndex]
    [(P.subgroupOf Q).FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    subgroupHomComplexTransfer P Q hPQ X V ≫ subgroupHomComplexTransfer Q T hQT X V =
      subgroupHomComplexTransfer P T (hPQ.trans hQT) X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact subgroupHomTransfer_comp_linear P Q T hPQ hQT (X.X n) V

/-- The induced maps on the actual Hom-complex cohomology compose in every degree. -/
theorem subgroupHomCohomologyTransfer_comp (P Q T : Subgroup G)
    (hPQ : P ≤ Q) (hQT : Q ≤ T)
    [(P.subgroupOf T).FiniteIndex] [(Q.subgroupOf T).FiniteIndex]
    [(P.subgroupOf Q).FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) (n : ℕ) :
    HomologicalComplex.homologyMap (subgroupHomComplexTransfer P Q hPQ X V) n ≫
        HomologicalComplex.homologyMap (subgroupHomComplexTransfer Q T hQT X V) n =
      HomologicalComplex.homologyMap
        (subgroupHomComplexTransfer P T (hPQ.trans hQT) X V) n := by
  rw [← HomologicalComplex.homologyMap_comp, subgroupHomComplexTransfer_comp]

end Sharpness.OrdinaryCohomology
