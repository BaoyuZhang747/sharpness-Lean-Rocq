import Sharpness.Unconditional.FusionSystemGroupTransportSaturation
import Sharpness.Unconditional.FiniteGroupFusionSaturation

/-! Group-induced fusion on the literal domain of an injective group embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
variable {A : Type u} {G : Type v} [Group A] [Group G]

theorem FusionSystem.eq_of_isHom_iff (F E : FusionSystem A)
    (h : ∀ {P Q : Subgroup A} (f : P →* Q), F.IsHom f ↔ E.IsHom f) : F = E := by
  cases F
  cases E
  congr
  funext P Q f
  exact propext (h f)

theorem groupTransport_finiteGroupFusion_isHom_iff (H : Subgroup G) (e : A ≃* H)
    {P Q : Subgroup A} (f : P →* Q) :
    ((finiteGroupFusion H).groupTransport e).IsHom f ↔
      ∃ g : G, ∀ x : P, (e (f x).val).val = g * (e x.val).val * g⁻¹ := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro x
    have hh := hg (e.subgroupMap P x)
    simpa only [groupTransportHom_apply, MulEquiv.coe_subgroupMap_apply] using hh
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := (e.subgroupMap P).surjective y
    simpa only [groupTransportHom_apply, MulEquiv.coe_subgroupMap_apply] using hg x

def finiteGroupFusionAlong (i : A →* G) (hi : Function.Injective i) : FusionSystem A :=
  (finiteGroupFusion i.range).groupTransport (MonoidHom.ofInjective hi)

@[simp] theorem finiteGroupFusionAlong_isHom_iff (i : A →* G) (hi : Function.Injective i)
    {P Q : Subgroup A} (f : P →* Q) :
    (finiteGroupFusionAlong i hi).IsHom f ↔
      ∃ g : G, ∀ x : P, i (f x).val = g * i x.val * g⁻¹ :=
  groupTransport_finiteGroupFusion_isHom_iff i.range (MonoidHom.ofInjective hi) f

theorem finiteGroupFusion_transport_saturated [Finite A] [Finite G]
    (p : ℕ) [Fact p.Prime] (H : Sylow p G) (e : A ≃* H) :
    ((finiteGroupFusion (H : Subgroup G)).groupTransport e).Saturated p :=
  (finiteGroupFusion (H : Subgroup G)).groupTransport_saturated e p
    (finiteGroupFusion_saturated p H)

theorem finiteGroupFusionAlong_saturated [Finite A] [Finite G]
    (p : ℕ) [Fact p.Prime] (i : A →* G) (hi : Function.Injective i)
    (H : Sylow p G) (hH : i.range = (H : Subgroup G)) :
    (finiteGroupFusionAlong i hi).Saturated p := by
  let e : A ≃* H := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hH)
  have he : finiteGroupFusionAlong i hi =
      (finiteGroupFusion (H : Subgroup G)).groupTransport e := by
    apply FusionSystem.eq_of_isHom_iff
    intro P Q f
    rw [finiteGroupFusionAlong_isHom_iff, groupTransport_finiteGroupFusion_isHom_iff]
    rfl
  rw [he]
  exact finiteGroupFusion_transport_saturated p H e

end Sharpness
