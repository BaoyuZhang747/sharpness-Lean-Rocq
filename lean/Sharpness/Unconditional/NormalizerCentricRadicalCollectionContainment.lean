import Sharpness.Unconditional.NormalizerCentricRadicalCollectionAction

/-! Every centric radical subgroup of group-induced fusion contains each
ambient normal p-subgroup lying in the embedded p-group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory
variable {A : Type u} {G : Type v} [Group A] [Group G]

theorem normal_subgroup_le_of_normalizer_inter_le [Finite A]
    (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A) (O P : Subgroup A) [O.Normal]
    (h : Subgroup.normalizer (P : Set A) ⊓ O ≤ P) : O ≤ P := by
  by_contra hOP
  let U := P ⊔ O
  have hPU : P ≤ U := le_sup_left
  have hsmall : P.subgroupOf U ≠ ⊤ := by
    intro heq
    have hUP : U ≤ P := Subgroup.subgroupOf_eq_top.mp heq
    exact hOP (le_sup_right.trans hUP)
  have hgrowth := FusionSystem.proper_subgroup_lt_normalizer p (hA.to_subgroup U) hsmall
  obtain ⟨n, hnN, hnP⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hgrowth)
  have hn : n.val ∈ Subgroup.normalizer (P : Set A) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPU] at hnN
    exact hnN
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp n.property
  have hbN : b ∈ Subgroup.normalizer (P : Set A) := by
    have hh := (Subgroup.normalizer (P : Set A)).mul_mem
      ((Subgroup.normalizer (P : Set A)).inv_mem (Subgroup.le_normalizer ha)) hn
    rw [← hab] at hh
    simpa only [inv_mul_cancel_left] using hh
  apply hnP
  change n.val ∈ P
  rw [← hab]
  exact P.mul_mem ha (h ⟨hbN, hb⟩)

theorem finiteGroupFusionAlong_normal_le_of_centric_radical [Finite A]
    (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A)
    (i : A →* G) (hi : Function.Injective i)
    (O : Subgroup G) [O.Normal] (hO : IsPGroup p O) (hOi : O ≤ i.range)
    (P : Subgroup A) (hc : (finiteGroupFusionAlong i hi).IsCentric P)
    (hr : (finiteGroupFusionAlong i hi).IsRadical p P) : O ≤ P.map i := by
  let F := finiteGroupFusionAlong i hi
  let N := Subgroup.normalizer (P.map i : Set G)
  let J := O.subgroupOf N
  let φ := embeddedNormalizerToOrbitAut i hi P
  have hJ : IsPGroup p J := hO.comap_of_injective N.subtype Subtype.coe_injective
  letI : J.Normal := inferInstanceAs (O.comap N.subtype).Normal
  have himage : (J.map φ).Normal :=
    Subgroup.Normal.map inferInstance φ (embeddedNormalizerToOrbitAut_surjective i hi P)
  have hbot : J.map φ = ⊥ := hr (J.map φ) himage (hJ.map φ)
  have hC : Subgroup.centralizer (P : Set A) ≤ P := by
    simpa only [inf_top_eq] using hc P le_top (MulEquiv.refl P) (F.id_mem P)
  have hNP : Subgroup.normalizer (P : Set A) ⊓ O.comap i ≤ P := by
    rintro n ⟨hn, ho⟩
    have hnG : i n ∈ N := Subgroup.le_normalizer_map i ⟨n, hn, rfl⟩
    have hm : φ ⟨i n, hnG⟩ ∈ J.map φ := ⟨⟨i n, hnG⟩, ho, rfl⟩
    rw [hbot] at hm
    have hzero : F.normalizerToOrbitAut P ⟨n, hn⟩ = 1 := by
      rw [← embeddedNormalizerToOrbitAut_inner i hi P ⟨n, hn⟩ hnG]
      exact hm
    exact (F.relativeNormalizerToAut_eq_one_iff (T := ⊤) hC ⟨n, hn, trivial⟩).mp hzero
  have hOP : O.comap i ≤ P := normal_subgroup_le_of_normalizer_inter_le p hA _ P hNP
  intro g hg
  obtain ⟨a, ha⟩ := hOi hg
  have hao : a ∈ O.comap i := by
    change i a ∈ O
    rw [ha]
    exact hg
  exact ⟨a, hOP hao, ha⟩

end Sharpness
