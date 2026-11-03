import Sharpness.Unconditional.FiniteGroupFusionAutomorphisms
import Sharpness.Unconditional.CentralizerSaturationReceptive

/-! Conjugation sends the exact fusion extension domain into the preimage
of the automorphisms induced by the Sylow normalizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G] [Finite G]

abbrev finiteGroupNormalizerPreimage (S : Subgroup G) (Q : Subgroup S) :
    Subgroup (finiteGroupAmbientNormalizer S Q) :=
  ((finiteGroupFusion S).innerSylowSubgroup Q).comap (finiteGroupNormalizerAction S Q)

theorem finiteGroupNormalizerSubgroup_le_preimage (S : Subgroup G) (Q : Subgroup S) :
    finiteGroupNormalizerSubgroup S Q ≤ finiteGroupNormalizerPreimage S Q := by
  intro n hn
  refine ⟨(finiteGroupNormalizerEquiv S Q).symm ⟨n, hn⟩, ?_⟩
  exact (finiteGroupNormalizerAction_inner S Q ⟨n, hn⟩).symm

theorem finiteGroup_conjugated_intertwining (S : Subgroup G) {P Q : Subgroup S}
    (e : P ≃* Q) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹)
    (n : Subgroup.normalizer (P : Set S)) (t : Subgroup.normalizer (Q : Set S))
    (ht : ∀ x : P, e (P.normalizerMonoidHom n x) = Q.normalizerMonoidHom t (e x))
    (y : Q) :
    ((Q.normalizerMonoidHom t y).val : G) =
      (g*(n.val : G)*g⁻¹) * (y.val : G) * (g*(n.val : G)*g⁻¹)⁻¹ := by
  calc
    _ = ((e (P.normalizerMonoidHom n (e.symm y))).val : G) := by
      simpa only [MulEquiv.apply_symm_apply] using
        (congrArg (fun z : Q => (z.val : G)) (ht (e.symm y))).symm
    _ = g * ((P.normalizerMonoidHom n (e.symm y)).val : G) * g⁻¹ := hg _
    _ = (g*(n.val : G)*g⁻¹) * (g*((e.symm y).val : G)*g⁻¹) *
        (g*(n.val : G)*g⁻¹)⁻¹ := by
      change g * ((n.val : G) * ((e.symm y).val : G) * (n.val : G)⁻¹) * g⁻¹ = _
      group
    _ = _ := by rw [← hg (e.symm y), MulEquiv.apply_symm_apply]

theorem finiteGroupExtensionConjugation_mem (S : Subgroup G) {P Q : Subgroup S}
    (e : P ≃* Q) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹)
    (n : (finiteGroupFusion S).extensionDomainSubgroup e) :
    ∃ hn : g*(n.val : G)*g⁻¹ ∈ finiteGroupAmbientNormalizer S Q,
      finiteGroupNormalizerAction S Q ⟨g*(n.val : G)*g⁻¹, hn⟩ ∈
        (finiteGroupFusion S).innerSylowSubgroup Q := by
  rcases n with ⟨_, n, rfl, t, ht⟩
  have hc := finiteGroup_conjugated_intertwining S e g hg n t ht
  refine ⟨finiteGroup_automorphism_witness_normalizes S Q
    (Q.normalizerMonoidHom t) (g*(n.val : G)*g⁻¹) hc, t, ?_⟩
  ext y
  rw [finiteGroupNormalizerAction_apply]
  exact hc y

def finiteGroupExtensionConjugation (S : Subgroup G) {P Q : Subgroup S}
    (e : P ≃* Q) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹) :
    (finiteGroupFusion S).extensionDomainSubgroup e →* finiteGroupNormalizerPreimage S Q where
  toFun n := ⟨⟨g*(n.val : G)*g⁻¹,
    (finiteGroupExtensionConjugation_mem S e g hg n).choose⟩,
    (finiteGroupExtensionConjugation_mem S e g hg n).choose_spec⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]

@[simp]
theorem finiteGroupExtensionConjugation_apply (S : Subgroup G) {P Q : Subgroup S}
    (e : P ≃* Q) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹)
    (n : (finiteGroupFusion S).extensionDomainSubgroup e) :
    ((finiteGroupExtensionConjugation S e g hg n).val : G) = g*(n.val : G)*g⁻¹ := rfl

end Sharpness
