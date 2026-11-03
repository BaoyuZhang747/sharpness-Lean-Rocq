import Sharpness.Unconditional.FiniteGroupFusionNormalizer

/-! Full normalization makes the actual normalizer in a Sylow subgroup
Sylow in the ambient group normalizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G] [Finite G]

/-- The normalizer Sylow theorem underlying saturation of a group fusion system. -/
def finiteGroupNormalizerSylow (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (P : Subgroup S)
    (hP : (finiteGroupFusion (S : Subgroup G)).FullyNormalized P) :
    Sylow p (finiteGroupAmbientNormalizer (S : Subgroup G) P) where
  toSubgroup := finiteGroupNormalizerSubgroup (S : Subgroup G) P
  isPGroup' := (S.isPGroup'.to_subgroup (Subgroup.normalizer (P : Set S))).of_equiv
    (finiteGroupNormalizerEquiv (S : Subgroup G) P)
  is_maximal' {T} hT hNST := by
    let N := finiteGroupAmbientNormalizer (S : Subgroup G) P
    let U := T.map N.subtype
    have hPU : finiteGroupAmbientSubgroup (S : Subgroup G) P ≤ U := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨⟨a.val, Subgroup.le_normalizer ⟨a, ha, rfl⟩⟩, ?_, rfl⟩
      exact hNST a.property
    obtain ⟨g, hg⟩ := finiteGroup_pSubgroup_conjugates_into p S U (hT.map N.subtype)
    have hPg : (finiteGroupAmbientSubgroup (S : Subgroup G) P).map
        (MulAut.conj g).toMonoidHom ≤ S := (Subgroup.map_mono hPU).trans hg
    have hcard : Nat.card T ≤ Nat.card (Subgroup.normalizer (P : Set S)) :=
      (Nat.card_le_card_of_injective
        (finiteGroupConjugatedNormalizerMap (S : Subgroup G) P T g hPg hg)
        (finiteGroupConjugatedNormalizerMap_injective (S : Subgroup G) P T g hPg hg)).trans
          (hP (finiteGroupConjugate (S : Subgroup G) P g hPg)
            (finiteGroupConjugateEquiv (S : Subgroup G) P g hPg)
            (finiteGroupConjugateEquiv_allowed (S : Subgroup G) P g hPg))
    apply (Subgroup.eq_of_le_of_card_ge hNST ?_).symm
    exact hcard.trans_eq (Nat.card_congr (finiteGroupNormalizerEquiv (S : Subgroup G) P).toEquiv)

@[simp]
theorem finiteGroupNormalizerSylow_coe (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (P : Subgroup S)
    (hP : (finiteGroupFusion (S : Subgroup G)).FullyNormalized P) :
    (finiteGroupNormalizerSylow p S P hP :
      Subgroup (finiteGroupAmbientNormalizer (S : Subgroup G) P)) =
      finiteGroupNormalizerSubgroup (S : Subgroup G) P := rfl

theorem finiteGroupNormalizer_index (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (P : Subgroup S)
    (hP : (finiteGroupFusion (S : Subgroup G)).FullyNormalized P) :
    ¬ p ∣ (finiteGroupNormalizerSubgroup (S : Subgroup G) P).index :=
  (finiteGroupNormalizerSylow p S P hP).not_dvd_index

end Sharpness
