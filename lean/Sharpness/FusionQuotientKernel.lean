import Sharpness.Saturation
import Sharpness.CentralSupport
import Sharpness.QuotientAutomorphisms

/-! The central-quotient automorphism kernel on actual subgroups and its
trivial action at the simple functor's minimal subgroup (Lemma 3.3 Step 2). -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def automorphismToOrbitAut (P : Subgroup S) :
    F.automorphismSubgroup P →* Aut (F.toOrbit.obj ⟨P⟩) where
  toFun a := F.toOrbit.mapIso (F.isoOfMulEquiv a.val a.property)
  map_one' := by
    apply Iso.ext
    change F.toOrbit.map _ = 𝟙 _
    rw [← F.toOrbit.map_id]
    congr 1
  map_mul' a b := by
    apply Iso.ext
    change F.toOrbit.map _ = F.toOrbit.map _ ≫ F.toOrbit.map _
    rw [← F.toOrbit.map_comp]
    congr 1

theorem automorphismToOrbitAut_surjective (P : Subgroup S) :
    Function.Surjective (F.automorphismToOrbitAut P) := by
  intro a
  let e := F.groupEquivOfOrbitIso a
  refine ⟨⟨e, F.groupEquivOfOrbitIso_allowed a⟩, ?_⟩
  apply Iso.ext
  exact F.orbitRepresentative_map a.hom

theorem central_subgroupOf_normal {Z : Subgroup S} (hZ : F.CentralSubgroup Z)
    (P : Subgroup S) : (Z.subgroupOf P).Normal := by
  constructor
  intro z hz x
  change x.val * z.val * x.val⁻¹ ∈ Z
  have hc := Subgroup.mem_center_iff.mp (hZ.in_center hz) x.val
  change x.val * z.val = z.val * x.val at hc
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hz

theorem central_aut_fixed {Z P : Subgroup S} (hZ : F.CentralSubgroup Z) (hZP : Z ≤ P)
    (a : F.automorphismSubgroup P) (z : Z.subgroupOf P) : a.val z.val = z.val := by
  apply Subtype.ext
  exact F.central_fixed hZ a.val.toMonoidHom a.property hZP ⟨z.val.val, z.property⟩

variable {Z P : Subgroup S} (hZ : F.CentralSubgroup Z) (hZP : Z ≤ P)
    [(Z.subgroupOf P).Normal]

def centralQuotientAction :
    F.automorphismSubgroup P →* MulAut (P ⧸ Z.subgroupOf P) :=
  quotientAutomorphismAction (F.automorphismSubgroup P).subtype (Z.subgroupOf P)
    (F.central_aut_fixed hZ hZP)

def Gamma : Subgroup (F.automorphismSubgroup P) := (F.centralQuotientAction hZ hZP).ker

instance gamma_normal : (F.Gamma hZ hZP).Normal := inferInstanceAs
  ((F.centralQuotientAction hZ hZP).ker.Normal)

theorem gamma_isPGroup (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) :
    IsPGroup p (F.Gamma hZ hZP) :=
  quotient_kernel_isPGroup (F.automorphismSubgroup P).subtype (Z.subgroupOf P)
    (F.central_aut_fixed hZ hZP) p ((hS.to_subgroup P).to_subgroup _)
    Subtype.val_injective

def orbitGamma : Subgroup (Aut (F.toOrbit.obj ⟨P⟩)) :=
  (F.Gamma hZ hZP).map (F.automorphismToOrbitAut P)

instance orbitGamma_normal : (F.orbitGamma hZ hZP).Normal :=
  Subgroup.Normal.map inferInstance (F.automorphismToOrbitAut P)
    (F.automorphismToOrbitAut_surjective P)

theorem orbitGamma_isPGroup (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) :
    IsPGroup p (F.orbitGamma hZ hZP) :=
  (F.gamma_isPGroup hZ hZP p hS).map (F.automorphismToOrbitAut P)

omit [(Z.subgroupOf P).Normal] in
theorem central_kernel_trivial_on_minimal (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] (hS : IsPGroup p S)
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup) :
    letI := F.central_subgroupOf_normal hZ label.Q.as.subgroup
    ∀ a : F.Gamma hZ hZQ,
      M.push (F.automorphismToOrbitAut label.Q.as.subgroup a.val).hom = LinearMap.id := by
  letI := F.central_subgroupOf_normal hZ label.Q.as.subgroup
  let N : Subgroup (Aut label.Q) := F.orbitGamma hZ hZQ
  haveI : Finite (Aut label.Q) :=
    Finite.of_injective (fun a : Aut label.Q => a.hom) (fun a b h => Iso.ext h)
  obtain ⟨v, hv⟩ := label.nonzero
  have ht := @normal_p_subgroup_acts_trivially p _ k _ _ (Aut label.Q) _ _
    (M.Value label.Q) _ _ (M.automorphismAction label.Q) N
    (F.orbitGamma_normal hZ hZQ)
    (F.orbitGamma_isPGroup hZ hZQ p hS) v hv label.simple_at_Q
  intro a
  apply LinearMap.ext
  intro x
  exact ht ⟨F.automorphismToOrbitAut _ a.val, ⟨a.val, a.property, rfl⟩⟩ x

end Sharpness.FusionSystem
