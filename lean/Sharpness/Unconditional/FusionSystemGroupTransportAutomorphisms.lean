import Sharpness.Unconditional.FusionSystemGroupTransportNormalized

/-! The actual automorphism and inner-automorphism subgroups under transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
variable {S : Type u} {T : Type v} [Group S] [Group T]

theorem groupTransport_normalizerAut (e : S ≃* T) (P : Subgroup S)
    (n : Subgroup.normalizer (P : Set S)) :
    MulAut.congr (e.subgroupMap P) (P.normalizerMonoidHom n) =
      (P.map e.toMonoidHom).normalizerMonoidHom (groupTransportNormalizerEquiv e P n) := by
  ext x
  change e (n.val * e.symm x.val * n.val⁻¹) = e n.val * x.val * (e n.val)⁻¹
  simp

namespace FusionSystem
variable [Finite S] [Finite T] (F : FusionSystem T) (e : S ≃* T)

theorem groupTransport_automorphism_map (P : Subgroup S) :
    ((F.groupTransport e).automorphismSubgroup P).map
      (MulAut.congr (e.subgroupMap P)).toMonoidHom =
        F.automorphismSubgroup (P.map e.toMonoidHom) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    change F.IsHom a.toMonoidHom at ha
    refine ⟨(MulAut.congr (e.subgroupMap P)).symm a, ?_,
      (MulAut.congr (e.subgroupMap P)).apply_symm_apply a⟩
    change F.IsHom ((MulAut.congr (e.subgroupMap P))
      ((MulAut.congr (e.subgroupMap P)).symm a)).toMonoidHom
    simpa only [MulEquiv.apply_symm_apply] using ha

theorem groupTransport_innerSylow_map (P : Subgroup S) :
    ((F.groupTransport e).innerSylowSubgroup P).map
      (MulAut.congr (e.subgroupMap P)).toMonoidHom =
        F.innerSylowSubgroup (P.map e.toMonoidHom) := by
  ext a
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨groupTransportNormalizerEquiv e P n, (groupTransport_normalizerAut e P n).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨P.normalizerMonoidHom ((groupTransportNormalizerEquiv e P).symm n),
      ⟨_, rfl⟩, ?_⟩
    change MulAut.congr (e.subgroupMap P)
      (P.normalizerMonoidHom ((groupTransportNormalizerEquiv e P).symm n)) = _
    rw [groupTransport_normalizerAut, MulEquiv.apply_symm_apply]

theorem groupTransport_automorphism_relIndex (P : Subgroup S) :
    ((F.groupTransport e).innerSylowSubgroup P).relIndex
      ((F.groupTransport e).automorphismSubgroup P) =
      (F.innerSylowSubgroup (P.map e.toMonoidHom)).relIndex
        (F.automorphismSubgroup (P.map e.toMonoidHom)) := by
  rw [← F.groupTransport_innerSylow_map e P, ← F.groupTransport_automorphism_map e P]
  exact (Subgroup.relIndex_map_map_of_injective _ _
    (MulAut.congr (e.subgroupMap P)).injective).symm

end FusionSystem
end Sharpness
