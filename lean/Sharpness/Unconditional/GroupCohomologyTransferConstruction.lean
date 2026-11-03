import Sharpness.GroupCohomologyPull
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Transfer on native group cohomology

The transfer is the inverse of Shapiro's isomorphism followed by the map on
cohomology induced by the finite-index coinduction counit. The counit is the
actual coset-sum map supplied by Mathlib's induction/coinduction isomorphism.
No transfer law or cohomological conclusion is an assumption of this definition.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
open scoped BigOperators

variable {R G A : Type u} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A]

/-- The actual trace from coinduction to the original representation. -/
def coinductionTrace (H : Subgroup G) [H.FiniteIndex] (V : Rep.{u} R G) :
    Rep.coind H.subtype (Rep.res H.subtype V) ⟶ V := by
  classical
  exact (Rep.coindResAdjunction R H).counit.app V

/-- Naturality of the actual coinduction trace in the coefficient representation. -/
theorem coinductionTrace_naturality (H : Subgroup G) [H.FiniteIndex]
    {V W : Rep.{u} R G} (f : V ⟶ W) :
    (Rep.coindFunctor R H.subtype).map ((Rep.resFunctor H.subtype).map f) ≫
        coinductionTrace H W = coinductionTrace H V ≫ f := by
  classical
  exact (Rep.coindResAdjunction R H).counit.naturality f

/-- The induction counit evaluates a generator by the inverse group action. -/
theorem inductionCounit_mk (H : Subgroup G) (V : Rep.{u} R G) (g : G) (a : V) :
    ((Rep.indResAdjunction R H.subtype).counit.app V).hom
      (Representation.IndV.mk H.subtype (Rep.res H.subtype V).ρ g a) =
        V.ρ g⁻¹ a := by
  change ((Rep.indResHomEquiv H.subtype (Rep.res H.subtype V) V).symm
    (𝟙 (Rep.res H.subtype V))).hom _ = _
  simp [Rep.indResHomEquiv]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

set_option backward.isDefEq.respectTransparency false in
/-- The trace is the genuine sum over right cosets, with the usual coefficient action. -/
theorem coinductionTrace_apply (H : Subgroup G) [H.FiniteIndex] (V : Rep.{u} R G)
    (f : Rep.coind H.subtype (Rep.res H.subtype V)) :
    (coinductionTrace H V).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel H), V.ρ q.out⁻¹ (f.1 q.out) := by
  classical
  rw [coinductionTrace, Rep.coindResAdjunction_counit_app]
  change ((Rep.indResAdjunction R H.subtype).counit.app V).hom
    (Rep.coindToInd (Rep.res H.subtype V) f) = _
  rw [Rep.coindToInd_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  conv_lhs => rw [← Quotient.out_eq q]
  exact inductionCounit_mk H V q.out (f.1 q.out)

/-- On trivial coefficients, no group action remains in the coset sum. -/
theorem coinductionTrace_trivial_apply (H : Subgroup G) [H.FiniteIndex]
    (f : Rep.coind H.subtype (Rep.trivial R H A)) :
    (coinductionTrace H (Rep.trivial R G A)).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel H), f.1 q.out := by
  simpa using coinductionTrace_apply H (Rep.trivial R G A) f

set_option backward.isDefEq.respectTransparency false in
/-- Trace after the coinduction unit is multiplication by the subgroup index. -/
theorem coinductionTrace_unit_apply (H : Subgroup G) [H.FiniteIndex]
    (V : Rep.{u} R G) (a : V) :
    (coinductionTrace H V).hom
      (((Rep.resCoindAdjunction.{u} R H.subtype).unit.app V).hom a) = H.index • a := by
  classical
  have hu (g : G) :
      ((((Rep.resCoindAdjunction.{u} R H.subtype).unit.app V).hom a).1 g) = V.ρ g a :=
    rfl
  rw [coinductionTrace_apply]
  simp only [hu, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Finset.sum_const, Finset.card_univ]
  rw [QuotientGroup.card_quotient_rightRel, ← Nat.card_eq_fintype_card,
    ← H.index_eq_card]

/-- Corestriction for a finite-index subgroup and an arbitrary representation. -/
def corestriction (H : Subgroup G) [H.FiniteIndex] (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology (Rep.res H.subtype V) n ⟶ groupCohomology V n :=
  (groupCohomology.coindIso (Rep.res H.subtype V) n).inv ≫
    groupCohomology.map (MonoidHom.id G) (coinductionTrace H V) n

/-- Shapiro followed by corestriction is exactly the cohomology map of the trace. -/
theorem shapiro_corestriction (H : Subgroup G) [H.FiniteIndex]
    (V : Rep.{u} R G) (n : ℕ) :
    (groupCohomology.coindIso (Rep.res H.subtype V) n).hom ≫ corestriction H V n =
      groupCohomology.map (MonoidHom.id G) (coinductionTrace H V) n := by
  simp [corestriction]

/-- Transfer on the native cohomology of an arbitrary trivial coefficient module. -/
def transfer (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    value R H A n ⟶ value R G A n :=
  corestriction H (Rep.trivial R G A) n

/-- The subgroup-inclusion transfer with the exact subgroup types used by fusion systems. -/
def subgroupTransfer [Finite G] (P Q : Subgroup G) (h : P ≤ Q) (n : ℕ) :
    value R P A n →ₗ[R] value R Q A n :=
  ((pull (R := R) (A := A) (Subgroup.subgroupOfEquivOfLe h).toMonoidHom n) ≫
    transfer (R := R) (A := A) (P.subgroupOf Q) n).hom

end Sharpness.OrdinaryCohomology
