import Sharpness.Unconditional.SimpleMackey
import Sharpness.SimpleTransport

/-!
The minimal subgroups of an actual simple full Mackey functor are precisely
the fusion conjugates of any least-order nonzero subgroup. This is the full
minimal-support assertion of manuscript Lemma `lem:minimal-simple`, proved
from the Mackey identities without simple-functor classification.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

/-- A minimal subgroup has nonzero value and zero value at every proper
subgroup. This is inclusion-minimality, not a least-order hypothesis. -/
def IsMinimalSupport (P : Subgroup S) : Prop :=
  (∃ x : M.Value (F.toOrbit.obj ⟨P⟩), x ≠ 0) ∧
    ∀ L : Subgroup S, L < P → ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0

/-- Fusion conjugacy is exactly isomorphism of the corresponding objects
of the actual orbit category. -/
theorem isConjugate_iff_orbit_iso (Q P : Subgroup S) :
    F.isoSystem.IsConjugate Q P ↔
      Nonempty (F.toOrbit.obj ⟨Q⟩ ≅ F.toOrbit.obj ⟨P⟩) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨F.toOrbit.mapIso (F.isoOfMulEquiv e he)⟩
  · rintro ⟨e⟩
    exact ⟨F.groupEquivOfOrbitIso e, F.groupEquivOfOrbitIso_allowed e⟩

variable {F M}

private theorem nonzero_of_orbit_iso {Q P : F.Orbit} (e : Q ≅ P)
    (hQ : ∃ x : M.Value Q, x ≠ 0) : ∃ x : M.Value P, x ≠ 0 := by
  obtain ⟨x, hx⟩ := hQ
  refine ⟨M.isoLinearEquiv e x, ?_⟩
  intro h
  apply hx
  exact (M.isoLinearEquiv e).injective (h.trans (map_zero _).symm)

variable (F M) (Q : Subgroup S)
    (simple : M.IsSimple)
    (nonzero : ∃ x : M.Value (F.toOrbit.obj ⟨Q⟩), x ≠ 0)
    (small_zero : ∀ L : Subgroup S, Nat.card L < Nat.card Q →
      ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0)

include nonzero small_zero

/-- Every fusion conjugate of a least-order nonzero subgroup is minimal.
This implication does not require simplicity. -/
theorem isMinimalSupport_of_isConjugate (P : Subgroup S)
    (hP : F.isoSystem.IsConjugate Q P) : F.IsMinimalSupport M P := by
  obtain ⟨e, he⟩ := hP
  have hcard : Nat.card Q = Nat.card P := Nat.card_congr e.toEquiv
  refine ⟨nonzero_of_orbit_iso (F.toOrbit.mapIso (F.isoOfMulEquiv e he)) nonzero, ?_⟩
  intro L hL x
  apply small_zero L _ x
  rw [hcard]
  have hle : Nat.card L ≤ Nat.card P :=
    F.orbitOrder_mono (F.toOrbit.map (F.inclusion hL.le))
  exact lt_of_le_of_ne hle (fun h => hL.ne (Subgroup.eq_of_le_of_card_ge hL.le h.ge))

include simple

/-- Generation by transfers from the least-order nonzero fusion class
forces every inclusion-minimal nonzero subgroup to belong to that class. -/
theorem isConjugate_of_isMinimalSupport (P : Subgroup S)
    (hP : F.IsMinimalSupport M P) : F.isoSystem.IsConjugate Q P := by
  classical
  have hsmall : ∀ L : F.Orbit,
      F.orbitOrder L < F.orbitOrder (F.toOrbit.obj ⟨Q⟩) →
      ∀ x : M.Value L, x = 0 := fun L h => small_zero L.as.subgroup h
  have hgen := F.simple_inclusion_generation M (F.toOrbit.obj ⟨Q⟩)
    hsmall simple nonzero (F.toOrbit.obj ⟨P⟩)
  have hex : ∃ L : F.MinimalInclusionIndex (F.toOrbit.obj ⟨Q⟩)
      (F.toOrbit.obj ⟨P⟩), True := by
    by_contra h
    have hbot : (⨆ L : F.MinimalInclusionIndex (F.toOrbit.obj ⟨Q⟩)
        (F.toOrbit.obj ⟨P⟩), LinearMap.range (M.push (F.minimalInclusion L))) = ⊥ := by
      apply bot_unique
      exact iSup_le fun L => (h ⟨L, trivial⟩).elim
    obtain ⟨x, hx⟩ := hP.1
    have hxmem : x ∈ (⊥ : Submodule k (M.Value (F.toOrbit.obj ⟨P⟩))) := by
      rw [← hbot, hgen]
      trivial
    exact hx hxmem
  obtain ⟨L, _⟩ := hex
  obtain ⟨e⟩ := L.property.2
  have hLP : L.val = P := by
    by_contra hne
    obtain ⟨x, hx⟩ := nonzero_of_orbit_iso e nonzero
    exact hx (hP.2 L.val (lt_of_le_of_ne L.property.1 hne) x)
  apply (F.isConjugate_iff_orbit_iso Q P).mpr
  simpa only [← hLP] using (show Nonempty (F.toOrbit.obj ⟨Q⟩ ≅
    F.toOrbit.obj ⟨L.val⟩) from ⟨e⟩)

/-- The precise minimal-support equivalence, with only simplicity and the
stated least-order choice as hypotheses. -/
theorem isMinimalSupport_iff_isConjugate (P : Subgroup S) :
    F.IsMinimalSupport M P ↔ F.isoSystem.IsConjugate Q P :=
  ⟨F.isConjugate_of_isMinimalSupport M Q simple nonzero small_zero P,
    F.isMinimalSupport_of_isConjugate M Q nonzero small_zero P⟩

/-- The set of all minimal subgroups is exactly the chosen fusion class. -/
theorem minimalSupport_eq_fusionClass :
    {P : Subgroup S | F.IsMinimalSupport M P} =
      {P : Subgroup S | F.isoSystem.IsConjugate Q P} := by
  ext P
  exact F.isMinimalSupport_iff_isConjugate M Q simple nonzero small_zero P

/-- The automorphism representation at every subgroup of the minimal
fusion class is nonzero and has no proper nonzero invariant submodule. -/
theorem simple_automorphismModule_of_isConjugate (P : Subgroup S)
    (hP : F.isoSystem.IsConjugate Q P) :
    (∃ x : M.Value (F.toOrbit.obj ⟨P⟩), x ≠ 0) ∧
      ∀ A : Submodule k (M.Value (F.toOrbit.obj ⟨P⟩)),
        (∀ g : Aut (F.toOrbit.obj ⟨P⟩), ∀ x ∈ A,
          M.automorphismAction (F.toOrbit.obj ⟨P⟩) g x ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
  obtain ⟨e⟩ := (F.isConjugate_iff_orbit_iso Q P).mp hP
  refine ⟨nonzero_of_orbit_iso e nonzero, ?_⟩
  have hcard : F.orbitOrder (F.toOrbit.obj ⟨P⟩) =
      F.orbitOrder (F.toOrbit.obj ⟨Q⟩) :=
    le_antisymm (F.orbitOrder_mono e.inv) (F.orbitOrder_mono e.hom)
  intro A hA
  apply M.simple_at_minimal (F.toOrbit.obj ⟨P⟩) _ simple A hA
  intro L hL
  exact small_zero L.as.subgroup (hL.trans_eq hcard)

/-- Every minimal nonzero subgroup has a simple automorphism module. -/
theorem simple_automorphismModule_of_isMinimalSupport (P : Subgroup S)
    (hP : F.IsMinimalSupport M P) :
    (∃ x : M.Value (F.toOrbit.obj ⟨P⟩), x ≠ 0) ∧
      ∀ A : Submodule k (M.Value (F.toOrbit.obj ⟨P⟩)),
        (∀ g : Aut (F.toOrbit.obj ⟨P⟩), ∀ x ∈ A,
          M.automorphismAction (F.toOrbit.obj ⟨P⟩) g x ∈ A) →
        A = ⊥ ∨ A = ⊤ :=
  F.simple_automorphismModule_of_isConjugate M Q simple nonzero small_zero P
    (F.isConjugate_of_isMinimalSupport M Q simple nonzero small_zero P hP)

omit simple nonzero small_zero in
/-- The least-order subgroup used above exists for every actual simple
full Mackey functor; no supplied classification label is required. -/
theorem exists_least_nonzero_support (hsimple : M.IsSimple) :
    ∃ Q : Subgroup S,
      (∃ x : M.Value (F.toOrbit.obj ⟨Q⟩), x ≠ 0) ∧
      (∀ L : Subgroup S, Nat.card L < Nat.card Q →
        ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0) := by
  obtain ⟨Q, hQ, hsmall⟩ := M.exists_minimal_nonzero hsimple.1
  exact ⟨Q.as.subgroup, hQ, fun L h => hsmall (F.toOrbit.obj ⟨L⟩) h⟩

omit simple nonzero small_zero in
/-- Every simple full Mackey functor has one fusion class as its exact
set of minimal supports, with the least-order subgroup constructed here. -/
theorem exists_minimalSupport_fusionClass (hsimple : M.IsSimple) :
    ∃ Q : Subgroup S,
      (∃ x : M.Value (F.toOrbit.obj ⟨Q⟩), x ≠ 0) ∧
      (∀ L : Subgroup S, Nat.card L < Nat.card Q →
        ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0) ∧
      {P : Subgroup S | F.IsMinimalSupport M P} =
        {P : Subgroup S | F.isoSystem.IsConjugate Q P} := by
  obtain ⟨Q, hQ, hsmall⟩ := F.exists_least_nonzero_support M hsimple
  exact ⟨Q, hQ, hsmall, F.minimalSupport_eq_fusionClass M Q hsimple hQ hsmall⟩

end Sharpness.FusionSystem
