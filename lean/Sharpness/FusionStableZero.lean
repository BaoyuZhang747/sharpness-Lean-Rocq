import Sharpness.CentralizerZero

/-! Lemma 3.6 with the manuscript's generation, detection and centralizer
lemmas supplied by their concrete Lean proofs, rather than as hypotheses. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def groupEquivOfOrbitIso {P Q : F.Orbit} (e : P ≅ Q) :
    P.as.subgroup ≃* Q.as.subgroup :=
  MulEquiv.ofBijective (F.orbitRepresentative e.hom).val
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨F.injective _ (F.orbitRepresentative e.hom).property,
        le_antisymm (F.orbitOrder_mono e.hom) (F.orbitOrder_mono e.inv)⟩)

theorem groupEquivOfOrbitIso_allowed {P Q : F.Orbit} (e : P ≅ Q) :
    F.IsHom (F.groupEquivOfOrbitIso e).toMonoidHom :=
  (F.orbitRepresentative e.hom).property

variable {k : Type u} [Field k] (DP : F.DiazParkTraceInput (k := k))
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)

include DP p hS

/-- The concrete form of the stable-element vanishing argument for a
subsystem over T. The centric-inclusion hypothesis is exactly that in the
manuscript, and is supplied by Yalcin 8.11 for centralizer systems. -/
theorem simple_subsystem_stable_zero
    (H : FusionIsoSystem S) (T : Subgroup S)
    (subsystem : ∀ {L K : Subgroup S} (e : L ≃* K), H.Allowed e → F.IsHom e.toMonoidHom)
    (centric : ∀ L, L ≤ T → H.CentricIn T L → F.IsCentric L)
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (x : M.Value (F.toOrbit.obj ⟨T⟩))
    (stable : ∀ (L K : Subgroup S) (hL : L ≤ T) (hK : K ≤ T)
      (e : L ≃* K) (heH : H.Allowed e),
      M.pull (F.toOrbit.map (F.isoOfMulEquiv e (subsystem e heH)).hom)
        (M.pull (F.toOrbit.map (F.inclusion hK)) x) =
          M.pull (F.toOrbit.map (F.inclusion hL)) x) : x = 0 := by
  apply (restrictionProduct_injective_iff _).mp
    (F.simple_inclusion_detection M label.Q label.small_zero label.simple label.nonzero
      (F.toOrbit.obj ⟨T⟩)) x
  intro L
  obtain ⟨e₀⟩ := L.property.2
  have hLF : ¬ F.IsCentric L.val := by
    intro h
    exact noncentric
      ((F.isoSystem.centricIn_iff_of_iso (F.groupEquivOfOrbitIso e₀)
        (F.groupEquivOfOrbitIso_allowed e₀)).mpr h)
  have hLH : ¬ H.CentricIn T L.val := fun h => hLF (centric L.val L.property.1 h)
  obtain ⟨K, hK, e, heH, hbad⟩ := H.not_centricIn_witness hLH
  have heF := subsystem e heH
  have hmin : Nonempty (label.Q ≅ F.toOrbit.obj ⟨K⟩) :=
    ⟨e₀.trans (F.toOrbit.mapIso (F.isoOfMulEquiv e heF))⟩
  have hz := F.simple_centralizer_zero DP p hS M label T K hK hmin hbad
  have hs := stable L.val K L.property.1 hK e heH
  rw [hz, LinearMap.zero_apply, map_zero] at hs
  exact hs.symm

theorem simple_arrowStable_zero (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (x : (F.coefficientData M).arrowStable F.topOrbit F.toTop) : x.val = 0 := by
  apply F.simple_subsystem_stable_zero DP p hS M label F.isoSystem ⊤
    (fun _ he => he) (fun _ _ h => h) noncentric x.val
  intro L K hL hK e heH
  exact x.property (F.toOrbit.map (F.isoOfMulEquiv e heH).hom)

theorem simple_centric_limit_zero (BLO : F.AlperinInput)
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    Subsingleton (((F.coefficientData M).onFull F.centricProperty).limit) := by
  apply subsingleton_of_forall_eq 0
  intro x
  apply (F.stableElementsEquiv BLO M).injective
  apply Subtype.ext
  rw [map_zero]
  exact F.simple_arrowStable_zero DP p hS M label noncentric (F.stableElementsEquiv BLO M x)

theorem simple_higherLimit_zero_degree
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    (BLO : F.AlperinInput) (AKO : F.DegreeZeroInput (k := k))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    IsZero (higherLimit (F.centricCoefficient M) 0) := by
  have hz := F.simple_centric_limit_zero DP p hS M label BLO noncentric
  exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr hz) (AKO.AKO_III_5_3 M)

end Sharpness.FusionSystem
