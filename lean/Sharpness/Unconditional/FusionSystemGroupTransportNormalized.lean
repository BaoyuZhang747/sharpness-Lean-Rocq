import Sharpness.Unconditional.FusionSystemGroupTransport

/-! Normalizers, centralizers, and full normalization under group transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
variable {S : Type u} {T : Type v} [Group S] [Group T]

def groupTransportNormalizerEquiv (e : S ≃* T) (P : Subgroup S) :
    Subgroup.normalizer (P : Set S) ≃* Subgroup.normalizer (P.map e.toMonoidHom : Set T) :=
  (e.subgroupMap (Subgroup.normalizer (P : Set S))).trans
    (MulEquiv.subgroupCongr (Subgroup.map_equiv_normalizer_eq P e))

@[simp] theorem groupTransportNormalizerEquiv_apply (e : S ≃* T) (P : Subgroup S)
    (n : Subgroup.normalizer (P : Set S)) :
    (groupTransportNormalizerEquiv e P n).val = e n.val := rfl

theorem groupTransportNormalizer_card (e : S ≃* T) (P : Subgroup S) :
    Nat.card (Subgroup.normalizer (P.map e.toMonoidHom : Set T)) =
      Nat.card (Subgroup.normalizer (P : Set S)) :=
  (Nat.card_congr (groupTransportNormalizerEquiv e P).toEquiv).symm

theorem groupTransportCentralizer_map (e : S ≃* T) (P : Subgroup S) :
    (Subgroup.centralizer (P : Set S)).map e.toMonoidHom =
      Subgroup.centralizer (P.map e.toMonoidHom : Set T) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

def groupTransportCentralizerEquiv (e : S ≃* T) (P : Subgroup S) :
    Subgroup.centralizer (P : Set S) ≃* Subgroup.centralizer (P.map e.toMonoidHom : Set T) :=
  (e.subgroupMap (Subgroup.centralizer (P : Set S))).trans
    (MulEquiv.subgroupCongr (groupTransportCentralizer_map e P))

theorem groupTransportCentralizer_card (e : S ≃* T) (P : Subgroup S) :
    Nat.card (Subgroup.centralizer (P.map e.toMonoidHom : Set T)) =
      Nat.card (Subgroup.centralizer (P : Set S)) :=
  (Nat.card_congr (groupTransportCentralizerEquiv e P).toEquiv).symm

def groupTransportUnmapEquiv (e : S ≃* T) {P Q : Subgroup S}
    (a : P.map e.toMonoidHom ≃* Q.map e.toMonoidHom) : P ≃* Q :=
  (e.subgroupMap P).trans (a.trans (e.subgroupMap Q).symm)

@[simp] theorem groupTransportEquiv_unmap (e : S ≃* T) {P Q : Subgroup S}
    (a : P.map e.toMonoidHom ≃* Q.map e.toMonoidHom) :
    groupTransportEquiv e (groupTransportUnmapEquiv e a) = a := by
  ext x
  simp [groupTransportEquiv, groupTransportUnmapEquiv]
  apply Subtype.ext
  exact e.apply_symm_apply _

namespace FusionSystem
variable [Finite S] [Finite T] (F : FusionSystem T) (e : S ≃* T)

theorem groupTransport_fullyNormalized_iff (P : Subgroup S) :
    (F.groupTransport e).FullyNormalized P ↔ F.FullyNormalized (P.map e.toMonoidHom) := by
  constructor
  · intro h R a ha
    obtain ⟨Q, rfl⟩ := (MulEquiv.mapSubgroup e).surjective R
    let b := groupTransportUnmapEquiv e a
    have hb : (F.groupTransport e).IsHom b.toMonoidHom := by
      change F.IsHom (groupTransportEquiv e b).toMonoidHom
      simpa only [b, groupTransportEquiv_unmap] using ha
    change Nat.card (Subgroup.normalizer (Q.map e.toMonoidHom : Set T)) ≤ _
    simpa only [groupTransportNormalizer_card] using h Q b hb
  · intro h Q a ha
    simpa only [groupTransportNormalizer_card] using
      h (Q.map e.toMonoidHom) (groupTransportEquiv e a) ha

theorem groupTransport_fullyCentralized_iff (P : Subgroup S) :
    (F.groupTransport e).FullyCentralized P ↔ F.FullyCentralized (P.map e.toMonoidHom) := by
  constructor
  · intro h R a ha
    obtain ⟨Q, rfl⟩ := (MulEquiv.mapSubgroup e).surjective R
    let b := groupTransportUnmapEquiv e a
    have hb : (F.groupTransport e).IsHom b.toMonoidHom := by
      change F.IsHom (groupTransportEquiv e b).toMonoidHom
      simpa only [b, groupTransportEquiv_unmap] using ha
    change Nat.card (Subgroup.centralizer (Q.map e.toMonoidHom : Set T)) ≤ _
    simpa only [groupTransportCentralizer_card] using h Q b hb
  · intro h Q a ha
    simpa only [groupTransportCentralizer_card] using
      h (Q.map e.toMonoidHom) (groupTransportEquiv e a) ha

end FusionSystem
end Sharpness
