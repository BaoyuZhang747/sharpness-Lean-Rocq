import Sharpness.Unconditional.GroupCohomologyTransferHom
import Sharpness.Unconditional.GroupCohomologyCosetTower

/-! Compatibility of the actual Hom-model transfer with arbitrary group
isomorphisms. The proof reindexes the genuine coset sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory QuotientGroup
open scoped BigOperators
variable {R G K : Type u} [CommRing R] [Group G] [Group K]

def homTransferRightCosetEquivOfMulEquiv (e : G ≃* K) (H : Subgroup G) :
    Quotient (rightRel H) ≃ Quotient (rightRel (H.map e.toMonoidHom)) :=
  Quotient.congr e.toEquiv fun a b => by
    rw [rightRel_apply, rightRel_apply]
    constructor
    · intro h
      exact ⟨b * a⁻¹, h, by simp⟩
    · rintro ⟨z, hz, he⟩
      have hz' : z = b * a⁻¹ := e.injective (by simpa using he)
      exact hz' ▸ hz

@[simp]
theorem homTransferRightCosetEquivOfMulEquiv_mk (e : G ≃* K) (H : Subgroup G) (g : G) :
    homTransferRightCosetEquivOfMulEquiv e H (Quotient.mk'' g) = Quotient.mk'' (e g) := rfl

theorem rightCosetTransport_sum (e : G ≃* K) (H : Subgroup G)
    {B : Type*} [AddCommMonoid B]
    [Fintype (Quotient (rightRel H))]
    [Fintype (Quotient (rightRel (H.map e.toMonoidHom)))]
    (f : G → B) (hf : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    (∑ q : Quotient (rightRel (H.map e.toMonoidHom)), f (e.symm q.out)) =
      ∑ q : Quotient (rightRel H), f q.out := by
  classical
  rw [← (homTransferRightCosetEquivOfMulEquiv e H).sum_comp (fun q => f (e.symm q.out))]
  apply Finset.sum_congr rfl
  intro q _
  apply rightCosetInvariant_eq f hf
  apply (homTransferRightCosetEquivOfMulEquiv e H).injective
  rw [homTransferRightCosetEquivOfMulEquiv_mk, e.apply_symm_apply, Quotient.out_eq']
  rw [Quotient.out_eq']

/-- Transport a restricted equivariant map along an arbitrary ambient
group isomorphism. Its underlying linear map is unchanged. -/
def transportRestrictedHom (e : G ≃* K) (H : Subgroup G)
    (X V : Rep R G) (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) :
    Rep.res (H.map e.toMonoidHom).subtype (Rep.res e.symm.toMonoidHom X) ⟶
      Rep.res (H.map e.toMonoidHom).subtype (Rep.res e.symm.toMonoidHom V) :=
  Rep.ofHom ⟨f.hom.toLinearMap, fun k => by
    have hk : e.symm k.val ∈ H := by
      obtain ⟨g, hg, he⟩ := k.property
      rw [← he]
      change e.symm (e g) ∈ H
      rw [e.symm_apply_apply]
      exact hg
    exact f.hom.isIntertwining' ⟨e.symm k.val, hk⟩⟩

theorem homTransferTransport_summand_invariant (H : Subgroup G) (X V : Rep R G)
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) (x : X)
    (h : H) (g : G) :
    V.ρ (((h : G) * g)⁻¹) (f.hom (X.ρ ((h : G) * g) x)) =
      V.ρ g⁻¹ (f.hom (X.ρ g x)) := by
  have hf := Rep.hom_comm_apply f h (X.ρ g x)
  change f.hom (X.ρ (h : G) (X.ρ g x)) = V.ρ (h : G) (f.hom (X.ρ g x)) at hf
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hf, Representation.inv_self_apply]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem homTransfer_transport_apply [Finite G] [Finite K]
    (e : G ≃* K) (H : Subgroup G) (X V : Rep R G)
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) (x : X) :
    (homTransfer (H.map e.toMonoidHom) (Rep.res e.symm.toMonoidHom X)
      (Rep.res e.symm.toMonoidHom V) (transportRestrictedHom e H X V f)).hom x =
        (homTransfer H X V f).hom x := by
  classical
  rw [homTransfer_apply, homTransfer_apply]
  change (∑ q : Quotient (rightRel (H.map e.toMonoidHom)),
      V.ρ (e.symm q.out⁻¹) (f.hom (X.ρ (e.symm q.out) x))) = _
  simpa only [map_inv] using rightCosetTransport_sum e H
    (fun g => V.ρ g⁻¹ (f.hom (X.ρ g x))) (homTransferTransport_summand_invariant H X V f x)

/-- Hom-model transfer commutes with arbitrary group-isomorphism
transport, as an equality of actual representation morphisms. -/
theorem homTransfer_transport [Finite G] [Finite K]
    (e : G ≃* K) (H : Subgroup G) (X V : Rep R G)
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) :
    homTransfer (H.map e.toMonoidHom) (Rep.res e.symm.toMonoidHom X)
        (Rep.res e.symm.toMonoidHom V) (transportRestrictedHom e H X V f) =
      (Rep.resFunctor e.symm.toMonoidHom).map (homTransfer H X V f) := by
  apply Rep.hom_ext
  ext x
  exact homTransfer_transport_apply e H X V f x

end Sharpness.OrdinaryCohomology
