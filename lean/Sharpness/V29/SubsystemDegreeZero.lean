import Sharpness.SubsystemCentric
import Sharpness.SubgroupAmbientGeometry
import Sharpness.FusionStableZero
import Sharpness.Unconditional.Alperin
import Sharpness.Unconditional.DegreeZero
import Sharpness.Unconditional.ProjectiveCoefficients
import Sharpness.V29.SimpleCentralizer
import Sharpness.V29.SimpleRestrictionFormula

/-! The manuscript Lemma 4.2 through the v2.9 trace-summand decomposition.
The subgroup transport, Alperin propagation, compatible-family comparison and
degree-zero derived-limit identification are shared proved foundations.
Both joint detection and centralizer vanishing below use the new summand route.
The former implementation remains unchanged in Sharpness.SubsystemStableZero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (T : Subgroup S) (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)

theorem simple_native_subsystem_stable_zero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (centric : ∀ P : Subgroup T, H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (x : M.Value (F.toOrbit.obj ⟨T⟩))
    (stable : ∀ (P Q : Subgroup T) (e : P ≃* Q) (he : H.IsHom e.toMonoidHom),
      M.pull (F.toOrbit.map ((F.subsystemRawFunctor T H h).map
        (H.isoOfMulEquiv e he).hom))
        (M.pull (F.toOrbit.map (F.inclusion (ambientSubgroup_le T Q))) x) =
          M.pull (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P))) x) : x = 0 := by
  have hQ : F.IsMinimalSupport M label.Q.as.subgroup :=
    F.isMinimalSupport_of_isConjugate M label.Q.as.subgroup label.nonzero
      (fun P hP => label.small_zero (F.toOrbit.obj ⟨P⟩) hP)
      label.Q.as.subgroup ⟨MulEquiv.refl _, F.isoSystem.id_mem _⟩
  apply F.simple_functor_restriction_detection_v29 M label.simple label.Q.as.subgroup hQ T x
  intro L₀ hLT hL
  let L : F.MinimalInclusionIndex label.Q (F.toOrbit.obj ⟨T⟩) :=
    ⟨L₀, hLT, (F.isConjugate_iff_orbit_iso _ _).mp hL⟩
  obtain ⟨e₀⟩ := L.property.2
  have hLF : ¬ F.IsCentric L.val := by
    intro hc
    exact noncentric
      ((F.isoSystem.centricIn_iff_of_iso (F.groupEquivOfOrbitIso e₀)
        (F.groupEquivOfOrbitIso_allowed e₀)).mpr hc)
  let P : Subgroup T := L.val.subgroupOf T
  have hP : ambientSubgroup T P = L.val := ambientSubgroup_subgroupOf T L.val L.property.1
  have hPH : ¬ H.IsCentric P := by
    intro hc
    exact hLF (hP ▸ centric P hc)
  obtain ⟨Q, _, e, he, hbad⟩ := H.isoSystem.not_centricIn_witness hPH
  have hbad' : ¬ Subgroup.centralizer (Q : Set T) ≤ Q := by
    simpa only [inf_top_eq] using hbad
  let eP := F.toOrbit.mapIso (F.subgroupEqualityIso hP.symm)
  let eQ := F.toOrbit.mapIso ((F.subsystemRawFunctor T H h).mapIso (H.isoOfMulEquiv e he))
  have hmin : Nonempty (label.Q ≅ F.toOrbit.obj ⟨ambientSubgroup T Q⟩) :=
    ⟨e₀.trans (eP.trans eQ)⟩
  have hz := F.simple_centralizer_zero_v29 M label.simple label.Q.as.subgroup hQ
    p hS (ambientSubgroup T Q) T
    ((F.isConjugate_iff_orbit_iso _ _).mpr hmin)
    (ambientSubgroup_le T Q) (ambient_bad_centralizer T Q hbad')
  have hs := stable P Q e he
  have hs' : M.pull (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P))) x = 0 :=
    hs.symm.trans ((congrArg (fun z => M.pull (F.toOrbit.map
      ((F.subsystemRawFunctor T H h).map (H.isoOfMulEquiv e he).hom)) z)
        (LinearMap.congr_fun hz x)).trans (map_zero _))
  have hinc : (F.subgroupEqualityIso hP.symm).hom ≫
      F.inclusion (ambientSubgroup_le T P) = F.inclusion L.property.1 := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro z
    rfl
  have hcomp : eP.hom ≫ F.toOrbit.map (F.inclusion (ambientSubgroup_le T P)) =
      F.toOrbit.map (F.inclusion L.property.1) :=
    (F.toOrbit.map_comp _ _).symm.trans (congrArg (fun f => F.toOrbit.map f) hinc)
  calc
    M.pull (F.toOrbit.map (F.inclusion L.property.1)) x =
        M.pull eP.hom (M.pull (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P))) x) :=
      (congrArg (fun f => M.pull f x) hcomp.symm).trans
        (LinearMap.congr_fun (M.pull_comp eP.hom
          (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P)))) x)
    _ = 0 := (congrArg (fun z => M.pull eP.hom z) hs').trans (map_zero _)

theorem subsystem_top_pull (P : Subgroup T)
    (v : (F.subsystemMackey T H h M).Value H.topOrbit) :
    M.pull (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P)))
      (M.pull (F.toOrbit.map (F.subsystemTopIso T H h).inv) v) =
        (F.subsystemMackey T H h M).pull (H.toTop (H.toOrbit.obj ⟨P⟩)) v := by
  have hs := congrArg (fun f => F.toOrbit.map f) (F.subsystem_top_inclusion_square T H h P)
  have hc := F.toOrbit.map_comp (F.inclusion (ambientSubgroup_le T P)) (F.subsystemTopIso T H h).inv
  exact (LinearMap.congr_fun (M.pull_comp
    (F.toOrbit.map (F.inclusion (ambientSubgroup_le T P)))
    (F.toOrbit.map (F.subsystemTopIso T H h).inv)) v).symm.trans
      (congrArg (fun f => M.pull f v) (hs.trans hc).symm)

theorem simple_native_subsystem_arrowStable_zero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (centric : ∀ P : Subgroup T, H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (v : (H.coefficientData (F.subsystemMackey T H h M)).arrowStable H.topOrbit H.toTop) :
    v.val = 0 := by
  have hz : M.pull (F.toOrbit.map (F.subsystemTopIso T H h).inv) v.val = 0 := by
    apply simple_native_subsystem_stable_zero F T H h M label p hS centric noncentric
    intro P Q e he
    rw [subsystem_top_pull F T H h M Q, subsystem_top_pull F T H h M P]
    exact v.property (H.toOrbit.map (H.isoOfMulEquiv e he).hom)
  have hv := congrArg (fun x => M.pull (F.toOrbit.map (F.subsystemTopIso T H h).hom) x) hz
  rw [map_zero, ← LinearMap.comp_apply, ← M.pull_comp, ← F.toOrbit.map_comp,
    (F.subsystemTopIso T H h).hom_inv_id, F.toOrbit.map_id, M.pull_id] at hv
  exact hv

theorem simple_native_subsystem_limit_zero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (centric : ∀ P : Subgroup T, H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (BLO : H.AlperinInput)
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    Subsingleton (((H.coefficientData (F.subsystemMackey T H h M)).onFull H.centricProperty).limit) := by
  apply subsingleton_of_forall_eq 0
  intro x
  apply (H.stableElementsEquiv BLO (F.subsystemMackey T H h M)).injective
  apply Subtype.ext
  rw [map_zero]
  exact simple_native_subsystem_arrowStable_zero F T H h M label p hS centric noncentric _

theorem simple_native_subsystem_higherLimit_zero_degree
    [EnoughProjectives (CoefficientCategory k H.CentricOrbit)]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (centric : ∀ P : Subgroup T, H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (BLO : H.AlperinInput) (AKO : H.DegreeZeroInput (k := k))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    IsZero (higherLimit ((F.subsystemCentricFunctor T H h centric).op ⋙ F.centricCoefficient M) 0) := by
  have hz := simple_native_subsystem_limit_zero F T H h M label p hS centric BLO noncentric
  have hzero := IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr hz)
    (AKO.AKO_III_5_3 (F.subsystemMackey T H h M))
  exact IsZero.of_iso hzero
    (higherLimitIso (F.subsystemCentricCoefficientIso T H h centric M) 0).symm

/-- Literal zeroth derived limit for a saturated subsystem, with all inputs proved. -/
theorem subsystemHigherLimitZero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (satH : H.Saturated p)
    (centric : ∀ P : Subgroup T,
      H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    IsZero (higherLimit
      ((F.subsystemCentricFunctor T H h centric).op ⋙ F.centricCoefficient M) 0) :=
  simple_native_subsystem_higherLimit_zero_degree F T H h M label p hS centric
    (H.alperinInput p (hS.to_subgroup T) satH) H.provedDegreeZeroInput noncentric

end Sharpness.FusionSystem.V29
