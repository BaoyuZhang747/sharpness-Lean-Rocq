import Sharpness.Unconditional.MinimalSupportRepresentation
import Sharpness.Unconditional.TraceFormulaInput

/-!
The four assertions of manuscript Lemma `lem:simple` for an arbitrary
inclusion-minimal nonzero subgroup. No least-order choice, classification
input, saturation or finite-dimensionality is supplied as a hypothesis.
The automorphism group of the fusion orbit object is the outer fusion
automorphism group; its module here is the actual group-algebra module.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped MonoidAlgebra

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (hM : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)

include hM hQ

/-- Inclusion-minimal support of a simple functor also has least nonzero order.
This is derived from simplicity, not added to the manuscript's hypotheses. -/
theorem minimalSupport_small_zero (L : Subgroup S) (hL : Nat.card L < Nat.card Q)
    (x : M.Value (F.toOrbit.obj ⟨L⟩)) : x = 0 := by
  obtain ⟨Q₀, hQ₀, hsmall⟩ := F.exists_least_nonzero_support M hM
  obtain ⟨e, _⟩ := F.isConjugate_of_isMinimalSupport M Q₀ hM hQ₀ hsmall Q hQ
  exact hsmall L (hL.trans_eq (Nat.card_congr e.toEquiv).symm) x

/-- Lemma `lem:simple` (i), with the given arbitrary minimal subgroup. -/
theorem simple_minimalSupport_class :
    {P : Subgroup S | F.IsMinimalSupport M P} =
      {P : Subgroup S | F.isoSystem.IsConjugate Q P} ∧
    ∀ L : Subgroup S, F.isoSystem.IsConjugate Q L →
      IsSimpleModule k[Aut (F.toOrbit.obj ⟨L⟩)]
        (Representation.asModule (M.automorphismAction (F.toOrbit.obj ⟨L⟩))) := by
  have hsmall := F.minimalSupport_small_zero M hM Q hQ
  exact ⟨F.minimalSupport_eq_fusionClass M Q hM hQ.1 hsmall,
    F.isSimpleModule_of_isConjugate M Q hM hQ.1 hsmall⟩

/-- Lemma `lem:simple` (ii): the sum of the actual inclusion-transfer images,
indexed literally by fusion conjugates of the given minimal subgroup. -/
theorem simple_minimal_transfer_generation (U : Subgroup S) :
    (⨆ (L : Subgroup S) (hLU : L ≤ U) (_ : F.isoSystem.IsConjugate Q L),
      LinearMap.range (M.push (F.toOrbit.map (F.inclusion hLU)))) = ⊤ := by
  have hsmall : ∀ P : F.Orbit,
      F.orbitOrder P < F.orbitOrder (F.toOrbit.obj ⟨Q⟩) →
        ∀ x : M.Value P, x = 0 :=
    fun P h => F.minimalSupport_small_zero M hM Q hQ P.as.subgroup h
  have hgen := F.simple_inclusion_generation M (F.toOrbit.obj ⟨Q⟩)
    hsmall hM hQ.1 (F.toOrbit.obj ⟨U⟩)
  apply top_unique
  rw [← hgen]
  refine iSup_le fun L => ?_
  exact le_iSup_of_le L.val (le_iSup_of_le L.property.1
    (le_iSup_of_le ((F.isConjugate_iff_orbit_iso Q L.val).mpr L.property.2) le_rfl))

/-- Lemma `lem:simple` (iii): restrictions to all included fusion conjugates
of the given minimal subgroup detect zero. -/
theorem simple_minimal_restriction_detection (U : Subgroup S)
    (x : M.Value (F.toOrbit.obj ⟨U⟩))
    (hx : ∀ (L : Subgroup S) (hLU : L ≤ U), F.isoSystem.IsConjugate Q L →
      M.pull (F.toOrbit.map (F.inclusion hLU)) x = 0) : x = 0 := by
  have hsmall : ∀ P : F.Orbit,
      F.orbitOrder P < F.orbitOrder (F.toOrbit.obj ⟨Q⟩) →
        ∀ x : M.Value P, x = 0 :=
    fun P h => F.minimalSupport_small_zero M hM Q hQ P.as.subgroup h
  apply (restrictionProduct_injective_iff _).mp
    (F.simple_inclusion_detection M (F.toOrbit.obj ⟨Q⟩)
      hsmall hM hQ.1 (F.toOrbit.obj ⟨U⟩)) x
  intro L
  exact hx L.val L.property.1
    ((F.isConjugate_iff_orbit_iso Q L.val).mpr L.property.2)

/-- The vanishing assertion at the end of Lemma `lem:simple` (iii). -/
theorem simple_minimal_value_zero (U : Subgroup S)
    (hnone : ∀ L : Subgroup S, F.isoSystem.IsConjugate Q L → ¬ L ≤ U)
    (x : M.Value (F.toOrbit.obj ⟨U⟩)) : x = 0 := by
  apply F.simple_minimal_restriction_detection M hM Q hQ U x
  intro L hLU hL
  exact (hnone L hL hLU).elim

/-- The least-order label required internally by the trace argument can be
constructed with the manuscript's given minimal subgroup as its object. -/
def simpleLabelAtMinimalSupport : F.SimpleLabel M where
  Q := F.toOrbit.obj ⟨Q⟩
  simple := hM
  nonzero := hQ.1
  small_zero P h := F.minimalSupport_small_zero M hM Q hQ P.as.subgroup h
  simple_at_Q A hA := M.simple_at_minimal (F.toOrbit.obj ⟨Q⟩)
    (fun P h => F.minimalSupport_small_zero M hM Q hQ P.as.subgroup h) hM A hA

/-- Lemma `lem:simple` (iv). The characteristic and p-group hypotheses are
essential; saturation is not assumed. The trace input is constructed internally. -/
theorem simple_minimal_centralizer_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (L T : Subgroup S)
    (hL : F.isoSystem.IsConjugate Q L) (hLT : L ≤ T)
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) :
    M.pull (F.toOrbit.map (F.inclusion hLT)) = 0 := by
  exact F.simple_centralizer_zero F.diazParkTraceInput p hS M
    (F.simpleLabelAtMinimalSupport M hM Q hQ) T L hLT
    ((F.isConjugate_iff_orbit_iso Q L).mp hL) bad

end Sharpness.FusionSystem
