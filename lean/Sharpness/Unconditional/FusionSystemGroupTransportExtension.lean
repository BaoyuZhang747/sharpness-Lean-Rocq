import Sharpness.Unconditional.FusionSystemGroupTransportAutomorphisms

/-! The exact saturation extension domain is carried across the group equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
variable {S : Type u} {T : Type v} [Group S] [Group T]

@[simp] theorem groupTransportEquiv_apply (e : S ≃* T) {P Q : Subgroup S}
    (a : P ≃* Q) (x : P) :
    groupTransportEquiv e a (e.subgroupMap P x) = e.subgroupMap Q (a x) := by
  simp [groupTransportEquiv]

@[simp] theorem groupTransportNormalizer_apply (e : S ≃* T) (P : Subgroup S)
    (n : Subgroup.normalizer (P : Set S)) (x : P) :
    (P.map e.toMonoidHom).normalizerMonoidHom (groupTransportNormalizerEquiv e P n)
        (e.subgroupMap P x) = e.subgroupMap P (P.normalizerMonoidHom n x) := by
  apply Subtype.ext
  change e n.val * e x.val * (e n.val)⁻¹ = e (n.val * x.val * n.val⁻¹)
  simp

theorem groupTransport_intertwining_iff (e : S ≃* T) {P Q : Subgroup S}
    (a : P ≃* Q) (n : Subgroup.normalizer (P : Set S))
    (t : Subgroup.normalizer (Q : Set S)) :
    (∀ x : P, a (P.normalizerMonoidHom n x) = Q.normalizerMonoidHom t (a x)) ↔
      ∀ y : P.map e.toMonoidHom,
        groupTransportEquiv e a
          ((P.map e.toMonoidHom).normalizerMonoidHom (groupTransportNormalizerEquiv e P n) y) =
        (Q.map e.toMonoidHom).normalizerMonoidHom (groupTransportNormalizerEquiv e Q t)
          (groupTransportEquiv e a y) := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := (e.subgroupMap P).surjective y
    simp only [groupTransportNormalizer_apply, groupTransportEquiv_apply, h x]
  · intro h x
    apply (e.subgroupMap Q).injective
    simpa only [groupTransportNormalizer_apply, groupTransportEquiv_apply] using h (e.subgroupMap P x)

namespace FusionSystem
variable [Finite S] [Finite T] (F : FusionSystem T) (e : S ≃* T)

theorem groupTransport_extensionDomain_iff {P Q : Subgroup S} (a : P ≃* Q) (s : S) :
    s ∈ (F.groupTransport e).extensionDomain a ↔
      e s ∈ F.extensionDomain (groupTransportEquiv e a) := by
  constructor
  · rintro ⟨n, rfl, t, ht⟩
    exact ⟨groupTransportNormalizerEquiv e P n, rfl, groupTransportNormalizerEquiv e Q t,
      (groupTransport_intertwining_iff e a n t).mp ht⟩
  · rintro ⟨n, hn, t, ht⟩
    let n₀ := (groupTransportNormalizerEquiv e P).symm n
    let t₀ := (groupTransportNormalizerEquiv e Q).symm t
    refine ⟨n₀, ?_, t₀, ?_⟩
    · apply e.injective
      calc
        e n₀.val = (groupTransportNormalizerEquiv e P n₀).val := rfl
        _ = n.val := congrArg Subtype.val ((groupTransportNormalizerEquiv e P).apply_symm_apply n)
        _ = e s := hn
    · apply (groupTransport_intertwining_iff e a n₀ t₀).mpr
      simpa only [n₀, t₀, MulEquiv.apply_symm_apply] using ht

end FusionSystem
end Sharpness
