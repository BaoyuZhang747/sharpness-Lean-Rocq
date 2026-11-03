import Sharpness.Saturation

/-! Pullback of an actual fusion system across a multiplicative equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
variable {S : Type u} {T : Type v} [Group S] [Group T]

def groupTransportHom (e : S ≃* T) {P Q : Subgroup S} (f : P →* Q) :
    P.map e.toMonoidHom →* Q.map e.toMonoidHom :=
  (e.subgroupMap Q).toMonoidHom.comp (f.comp (e.subgroupMap P).symm.toMonoidHom)

@[simp] theorem groupTransportHom_apply (e : S ≃* T) {P Q : Subgroup S}
    (f : P →* Q) (x : P) :
    groupTransportHom e f (e.subgroupMap P x) = e.subgroupMap Q (f x) := by
  simp [groupTransportHom]

@[simp] theorem groupTransportHom_id (e : S ≃* T) (P : Subgroup S) :
    groupTransportHom e (MonoidHom.id P) = MonoidHom.id _ := by
  ext x
  simp [groupTransportHom]

@[simp] theorem groupTransportHom_comp (e : S ≃* T) {P Q U : Subgroup S}
    (f : P →* Q) (g : Q →* U) :
    groupTransportHom e (g.comp f) = (groupTransportHom e g).comp (groupTransportHom e f) := by
  ext x
  simp [groupTransportHom]

def groupTransportEquiv (e : S ≃* T) {P Q : Subgroup S} (a : P ≃* Q) :
    P.map e.toMonoidHom ≃* Q.map e.toMonoidHom :=
  (e.subgroupMap P).symm.trans (a.trans (e.subgroupMap Q))

@[simp] theorem groupTransportEquiv_toMonoidHom (e : S ≃* T) {P Q : Subgroup S}
    (a : P ≃* Q) : (groupTransportEquiv e a).toMonoidHom = groupTransportHom e a.toMonoidHom := rfl

@[simp] theorem groupTransportEquiv_symm (e : S ≃* T) {P Q : Subgroup S} (a : P ≃* Q) :
    (groupTransportEquiv e a).symm = groupTransportEquiv e a.symm := rfl

theorem groupTransportHom_inclusion (e : S ≃* T) {P Q : Subgroup S} (h : P ≤ Q) :
    groupTransportHom e (subgroupInclusion P Q h) =
      subgroupInclusion _ _ (Subgroup.map_mono h) := by
  ext x
  change e (e.symm x.val) = x.val
  exact e.apply_symm_apply _

def FusionSystem.groupTransport (F : FusionSystem T) (e : S ≃* T) : FusionSystem S where
  IsHom f := F.IsHom (groupTransportHom e f)
  injective f hf := by
    intro x y h
    apply (e.subgroupMap _).injective
    apply F.injective _ hf
    simp only [groupTransportHom_apply, h]
  id_mem P := by rw [groupTransportHom_id]; exact F.id_mem _
  comp_mem f g hf hg := by rw [groupTransportHom_comp]; exact F.comp_mem _ _ hf hg
  inclusion_mem h := by rw [groupTransportHom_inclusion]; exact F.inclusion_mem _
  conjugation_mem P Q s h := by
    have hm : ∀ x ∈ P.map e.toMonoidHom, (e s)⁻¹*x*(e s) ∈ Q.map e.toMonoidHom := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨s⁻¹*x*s, h x hx, by simp⟩
    have heq : groupTransportHom e (subgroupConjugation P Q s h) =
        subgroupConjugation _ _ (e s) hm := by
      ext x
      simp [groupTransportHom, subgroupConjugation]
    rw [heq]
    exact F.conjugation_mem _ _ _ _
  inverse_mem a ha := F.inverse_mem (groupTransportEquiv e a) ha
  codomain_restrict_mem f hf h g hg := by
    apply F.codomain_restrict_mem _ hf (Subgroup.map_mono h) (groupTransportHom e g)
    rw [← groupTransportHom_inclusion e h, ← groupTransportHom_comp, hg]

@[simp] theorem FusionSystem.groupTransport_isHom_iff (F : FusionSystem T) (e : S ≃* T)
    {P Q : Subgroup S} (f : P →* Q) :
    (F.groupTransport e).IsHom f ↔ F.IsHom (groupTransportHom e f) := Iff.rfl

end Sharpness
