import Sharpness.Unconditional.FiniteGroupFusionNormalizerSylow

/-! The ambient normalizer maps onto the actual group-fusion automorphism group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {G : Type u} [Group G]

@[simp]
theorem finiteGroupAmbientEquiv_symm_apply (S : Subgroup G) (P : Subgroup S)
    (x : finiteGroupAmbientSubgroup S P) :
    ((finiteGroupAmbientEquiv S P).symm x).val.val = x.val :=
  congrArg Subtype.val ((finiteGroupAmbientEquiv S P).apply_symm_apply x)

def finiteGroupNormalizerAction (S : Subgroup G) (P : Subgroup S) :
    finiteGroupAmbientNormalizer S P →* MulAut P where
  toFun n := (finiteGroupAmbientEquiv S P).trans
    (((finiteGroupAmbientSubgroup S P).normalizerMonoidHom n).trans
      (finiteGroupAmbientEquiv S P).symm)
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp

@[simp]
theorem finiteGroupNormalizerAction_apply (S : Subgroup G) (P : Subgroup S)
    (n : finiteGroupAmbientNormalizer S P) (x : P) :
    ((finiteGroupNormalizerAction S P n x).val : G) = n.val * (x.val : G) * n.val⁻¹ := by
  change ((finiteGroupAmbientEquiv S P).symm
    ((finiteGroupAmbientSubgroup S P).normalizerMonoidHom n (finiteGroupAmbientEquiv S P x))).val.val = _
  rw [finiteGroupAmbientEquiv_symm_apply]
  rfl

theorem finiteGroupNormalizerAction_allowed (S : Subgroup G) (P : Subgroup S)
    (n : finiteGroupAmbientNormalizer S P) :
    (finiteGroupFusion S).IsHom (finiteGroupNormalizerAction S P n).toMonoidHom :=
  ⟨n.val, finiteGroupNormalizerAction_apply S P n⟩

/-- A conjugation realizing an actual automorphism normalizes the ambient subgroup. -/
theorem finiteGroup_automorphism_witness_normalizes (S : Subgroup G) (P : Subgroup S)
    (e : P ≃* P) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹) :
    g ∈ finiteGroupAmbientNormalizer S P := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(e ⟨a, ha⟩).val, (e ⟨a, ha⟩).property, hg ⟨a, ha⟩⟩
  · rintro _ ⟨a, ha, rfl⟩
    let x := e.symm ⟨a, ha⟩
    refine ⟨(x.val : G), ⟨x.val, x.property, rfl⟩, ?_⟩
    change g * (x.val : G) * g⁻¹ = (a : G)
    rw [← hg x]
    exact congrArg (fun z : P => (z.val : G)) (e.apply_symm_apply ⟨a, ha⟩)

variable [Finite G]

def finiteGroupNormalizerToAut (S : Subgroup G) (P : Subgroup S) :
    finiteGroupAmbientNormalizer S P →* (finiteGroupFusion S).automorphismSubgroup P :=
  (finiteGroupNormalizerAction S P).codRestrict _ (finiteGroupNormalizerAction_allowed S P)

theorem finiteGroupNormalizerToAut_surjective (S : Subgroup G) (P : Subgroup S) :
    Function.Surjective (finiteGroupNormalizerToAut S P) := by
  intro e
  obtain ⟨g, hg⟩ := e.property
  refine ⟨⟨g, finiteGroup_automorphism_witness_normalizes S P e.val g hg⟩, ?_⟩
  apply Subtype.ext
  ext x
  exact (finiteGroupNormalizerAction_apply S P _ x).trans (hg x).symm

@[simp]
theorem finiteGroupNormalizerAction_inner (S : Subgroup G) (P : Subgroup S)
    (n : finiteGroupNormalizerSubgroup S P) :
    finiteGroupNormalizerAction S P n.val =
      P.normalizerMonoidHom ((finiteGroupNormalizerEquiv S P).symm n) := by
  ext x
  rw [finiteGroupNormalizerAction_apply]
  rfl

theorem finiteGroupNormalizerToAut_map (S : Subgroup G) (P : Subgroup S) :
    (finiteGroupNormalizerSubgroup S P).map (finiteGroupNormalizerToAut S P) =
      ((finiteGroupFusion S).innerSylowSubgroup P).subgroupOf
        ((finiteGroupFusion S).automorphismSubgroup P) := by
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(finiteGroupNormalizerEquiv S P).symm ⟨n, hn⟩, ?_⟩
    exact (finiteGroupNormalizerAction_inner S P ⟨n, hn⟩).symm
  · rintro ⟨n, hn⟩
    refine ⟨(finiteGroupNormalizerEquiv S P n).val,
      (finiteGroupNormalizerEquiv S P n).property, ?_⟩
    apply Subtype.ext
    change finiteGroupNormalizerAction S P (finiteGroupNormalizerEquiv S P n).val = a.val
    rw [finiteGroupNormalizerAction_inner, MulEquiv.symm_apply_apply]
    exact hn

theorem finiteGroupFusion_fullyNormalized_sylow (p : ℕ) [Fact p.Prime]
    (S : Sylow p G) (P : Subgroup S)
    (hP : (finiteGroupFusion (S : Subgroup G)).FullyNormalized P) :
    ¬ p ∣ ((finiteGroupFusion (S : Subgroup G)).innerSylowSubgroup P).relIndex
      ((finiteGroupFusion (S : Subgroup G)).automorphismSubgroup P) := by
  change ¬ p ∣ (((finiteGroupFusion (S : Subgroup G)).innerSylowSubgroup P).subgroupOf
    ((finiteGroupFusion (S : Subgroup G)).automorphismSubgroup P)).index
  rw [← finiteGroupNormalizerToAut_map]
  intro hd
  exact finiteGroupNormalizer_index p S P hP
    (hd.trans (Subgroup.index_map_dvd _ (finiteGroupNormalizerToAut_surjective (S : Subgroup G) P)))

end Sharpness
