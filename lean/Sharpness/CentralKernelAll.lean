import Sharpness.KernelRestriction

/-! Lemma 3.3 Step 2, completed on all actual values: the normal quotient
kernel is trivial first at every minimal conjugate and then everywhere by
the manuscript's proved restriction detection. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (hS : IsPGroup p S) (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M) {Z : Subgroup S} (hZ : F.CentralSubgroup Z)
    (hZQ : Z ≤ label.Q.as.subgroup)

include hS hZQ

theorem central_kernel_pull_trivial (P : Subgroup S) (hZP : Z ≤ P) :
    letI := F.central_subgroupOf_normal hZ P
    ∀ a : F.Gamma hZ hZP,
      M.pull (F.automorphismToOrbitAut P a.val).hom = LinearMap.id := by
  letI := F.central_subgroupOf_normal hZ P
  intro a
  apply action_eq_id_of_detected
    (fun L : F.MinimalInclusionIndex label.Q (F.toOrbit.obj ⟨P⟩) =>
      M.pull (F.minimalInclusion L))
    (F.simple_inclusion_detection M label.Q label.small_zero label.simple label.nonzero _)
  intro L
  obtain ⟨e⟩ := L.property.2
  have hZL : Z ≤ L.val := (F.central_containment_iff hZ (F.groupEquivOfOrbitIso e)
    (F.groupEquivOfOrbitIso_allowed e)).mp hZQ
  letI := F.central_subgroupOf_normal hZ L.val
  let aL := F.gammaRestriction hZ hZP a hZL L.property.1
  let alphaL := F.automorphismToOrbitAut L.val aL.val
  have hpush : M.push alphaL.hom = LinearMap.id :=
    F.central_kernel_trivial_on_conjugate M label p hS hZ hZQ L.val e aL
  have hpull := M.push_pull_iso alphaL
  rw [hpush, LinearMap.id_comp] at hpull
  have square := F.gamma_inclusion_square hZ hZP a hZL L.property.1
  have maps := congrArg (fun f => M.pull f) square
  rw [M.pull_comp, M.pull_comp] at maps
  change (M.pull (F.minimalInclusion L)).comp
      (M.pull (F.automorphismToOrbitAut P a.val).hom) =
    (M.pull alphaL.hom).comp (M.pull (F.minimalInclusion L)) at maps
  rw [hpull, LinearMap.id_comp] at maps
  exact maps

theorem central_kernel_push_trivial (P : Subgroup S) (hZP : Z ≤ P) :
    letI := F.central_subgroupOf_normal hZ P
    ∀ a : F.Gamma hZ hZP,
      M.push (F.automorphismToOrbitAut P a.val).hom = LinearMap.id := by
  letI := F.central_subgroupOf_normal hZ P
  intro a
  have h := M.push_pull_iso (F.automorphismToOrbitAut P a.val)
  rw [F.central_kernel_pull_trivial p hS M label hZ hZQ P hZP a, LinearMap.comp_id] at h
  exact h

end Sharpness.FusionSystem
