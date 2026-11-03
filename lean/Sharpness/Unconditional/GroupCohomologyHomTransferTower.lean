import Sharpness.Unconditional.GroupCohomologyAmbientTransfer
import Sharpness.Unconditional.GroupCohomologyCosetTower

/-! Transitivity of actual transfers on equivariant Hom spaces, proved by
regrouping the native finite-index coset sums. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
open scoped BigOperators

variable {R G : Type u} [CommRing R] [Group G]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The summand in transfer depends only on its right coset. -/
theorem homTransfer_summand_invariant (P : Subgroup G) (X V : Rep.{u} R G)
    (f : Rep.res P.subtype X ⟶ Rep.res P.subtype V) (x : X) (p : P) (g : G) :
    V.ρ ((p : G) * g)⁻¹ (f.hom (X.ρ ((p : G) * g) x)) =
      V.ρ g⁻¹ (f.hom (X.ρ g x)) := by
  have hf := Rep.hom_comm_apply f p (X.ρ g x)
  change f.hom (X.ρ p (X.ρ g x)) = V.ρ p (f.hom (X.ρ g x)) at hf
  rw [map_mul, Module.End.mul_apply, hf, mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- Pointwise formula for transfer between the actual subgroup types. -/
theorem subgroupHomTransfer_apply (P Q : Subgroup G) (hPQ : P ≤ Q)
    [(P.subgroupOf Q).FiniteIndex] (X V : Rep.{u} R G)
    (f : Rep.res P.subtype X ⟶ Rep.res P.subtype V) (x : X) :
    (subgroupHomTransfer P Q hPQ X V f).hom x =
      ∑ b : Quotient (QuotientGroup.rightRel (P.subgroupOf Q)),
        V.ρ (b.out : G)⁻¹ (f.hom (X.ρ (b.out : G) x)) := by
  exact homTransfer_apply (P.subgroupOf Q) (Rep.res Q.subtype X)
    (Rep.res Q.subtype V) (subgroupHomToNested P Q hPQ X V f) x

/-- Transfer through a nested subgroup agrees with direct transfer to the
ambient group, before taking cohomology and for arbitrary representations. -/
theorem homTransfer_tower (P Q : Subgroup G) (hPQ : P ≤ Q)
    [P.FiniteIndex] [Q.FiniteIndex] (X V : Rep.{u} R G)
    (f : Rep.res P.subtype X ⟶ Rep.res P.subtype V) :
    homTransfer Q X V (subgroupHomTransfer P Q hPQ X V f) =
      homTransfer P X V f := by
  apply Rep.hom_ext
  ext x
  change (homTransfer Q X V (subgroupHomTransfer P Q hPQ X V f)).hom x =
    (homTransfer P X V f).hom x
  rw [homTransfer_apply, homTransfer_apply]
  rw [rightCosetTower_sum hPQ
    (fun g : G => V.ρ g⁻¹ (f.hom (X.ρ g x)))
    (fun p g => homTransfer_summand_invariant P X V f x p g)]
  apply Finset.sum_congr rfl
  intro a _
  rw [subgroupHomTransfer_apply, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]

/-- The preceding equality as an equality of linear maps between Hom modules. -/
theorem homTransfer_tower_linear (P Q : Subgroup G) (hPQ : P ≤ Q)
    [P.FiniteIndex] [Q.FiniteIndex] (X V : Rep.{u} R G) :
    (homTransfer Q X V).comp (subgroupHomTransfer P Q hPQ X V) =
      homTransfer P X V := by
  apply LinearMap.ext
  intro f
  exact homTransfer_tower P Q hPQ X V f

/-- Transitivity on Hom cochain complexes of any ambient chain complex. -/
theorem homComplexTransfer_tower (P Q : Subgroup G) (hPQ : P ≤ Q)
    [P.FiniteIndex] [Q.FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    subgroupHomComplexTransfer P Q hPQ X V ≫ homComplexTransfer Q X V =
      homComplexTransfer P X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact homTransfer_tower_linear P Q hPQ (X.X n) V

end Sharpness.OrdinaryCohomology
