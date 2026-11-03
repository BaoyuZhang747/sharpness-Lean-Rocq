import Sharpness.V29.ReductionArbitrary
import Sharpness.V29.SimpleCentralizer
import Sharpness.V29.SimpleRestrictionFormula
import Sharpness.Unconditional.CentralQuotientSharpness

/-! The central-quotient implication through the v2.9 simple-summand
vanishing and composition-series/filtered-colimit reduction.  The previously
proved actual quotient Mackey construction and collection comparison are
shared unchanged. Their own earlier lower-level proof witnesses are retained. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

include hS hZ in
/-- If the minimal class misses the central subgroup, the actual trace
summands vanish and their restriction formulas force every centric value
to be zero. -/
theorem simple_centric_zero_of_central_missing
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)
    (hZQ : ¬ Z ≤ Q) (P : Subgroup S) (hPc : F.IsCentric P)
    (x : M.Value (F.toOrbit.obj ⟨P⟩)) : x = 0 := by
  apply F.simple_functor_restriction_detection_v29 M hM Q hQ P x
  intro L hLP hL
  obtain ⟨e, he⟩ := hL
  have hZL : ¬ Z ≤ L := fun h => hZQ ((F.central_containment_iff hZ e he).mpr h)
  have hZP := F.central_le_centric hZ hPc
  have bad : ¬ Subgroup.centralizer (L : Set S) ⊓ P ≤ L := by
    intro hc
    exact hZL ((le_inf (hZ.in_center.trans (Subgroup.center_le_centralizer _)) hZP).trans hc)
  have hz := F.simple_centralizer_zero_v29 M hM Q hQ p hS L P ⟨e, he⟩ hLP bad
  exact LinearMap.congr_fun hz x

include hS sat in
/-- Proposition `prop:central` with the actual quotient fusion system.
The reduction and missing-central-subgroup branch use the new manuscript
routes. The contains-central-subgroup branch reuses the proved quotient
functor, coefficient isomorphisms and collection restriction theorem. -/
theorem central_quotient_sharpness
    (sharp : (F.centralQuotient hZ).Sharp (R := PrimeField.{u} p)) :
    F.Sharp (R := PrimeField.{u} p) := by
  apply simple_reduction F p hS sat
  intro M hM
  let label := F.simpleLabel M hM
  by_cases hZQ : Z ≤ label.Q.as.subgroup
  · exact F.simple_central_acyclic_of_quotient_sharp_atomic hZ p hS sat
      (F.akoQuotientInput hZ p hS sat)
      (F.nonradical_atomic_higherLimits_zero p hS sat (PrimeField.{u} p))
      M label hZQ sharp
  · apply (Unconditional.finiteCategoryBarModel (PrimeField.{u} p)
      F.CentricOrbit).acyclic_of_values_zero (F.centricCoefficient M)
      (Unconditional.finiteCategoryBarComparison (PrimeField.{u} p) F.CentricOrbit)
    intro P x
    exact simple_centric_zero_of_central_missing F p hS hZ M hM
      label.Q.as.subgroup (simpleLabel_isMinimalSupport F p M hM)
      hZQ P.unop.obj.as.subgroup P.unop.property x

end Sharpness.FusionSystem.V29
