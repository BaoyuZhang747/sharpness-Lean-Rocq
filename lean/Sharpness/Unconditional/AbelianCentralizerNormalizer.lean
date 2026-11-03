import Sharpness.Unconditional.AbelianCentralizerKBridge
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! The joint K-normalizer is exactly the native centralizer normalizer. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

private theorem mem_ambientSubgroup_iff {T : Subgroup S} (P : Subgroup T) (x : T) :
    x.val ∈ ambientSubgroup T P ↔ x ∈ P := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (show y = x from Subtype.ext hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem abelianCentralizer_kNormalizer_eq (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    F.kNormalizer
      (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
      (F.abelianCentralizerJoinK E P) =
    ambientSubgroup (F.abelianCentralizerGroup E) (Subgroup.normalizer (P : Set (F.abelianCentralizerGroup E))) := by
  let T := F.abelianCentralizerGroup E
  let Z := F.abelianInCentralizer E
  let J := P ⊔ Z
  let A := ambientSubgroup T J
  let K := F.abelianCentralizerJoinK E P
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxK⟩ := (F.mem_kNormalizer_iff A K x).mp hx
    let a : K := ⟨F.kNormalizerAction A ⟨x, hxA⟩, hxK⟩
    have hxT : x ∈ T := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      let z' : Z := ⟨⟨z, F.abelian_le_centralizer E hz⟩, hz⟩
      have hfix := F.abelianCentralizerJoinK_fixes E P a z'
      change x * z * x⁻¹ = z at hfix
      calc
        z * x = (x * z * x⁻¹) * x := by rw [hfix]
        _ = x * z := by group
    have hxP : x ∈ Subgroup.normalizer (ambientSubgroup T P : Set S) := by
      intro y
      constructor
      · intro hy
        have hyA : y ∈ A := Subgroup.map_mono (show P ≤ J from le_sup_left) hy
        exact (F.abelianCentralizerJoinK_preserves E P a ⟨y, hyA⟩).mpr hy
      · intro hy
        have hconjA : x * y * x⁻¹ ∈ A := Subgroup.map_mono (show P ≤ J from le_sup_left) hy
        have hyA : y ∈ A := (hxA y).mpr hconjA
        exact (F.abelianCentralizerJoinK_preserves E P a ⟨y, hyA⟩).mp hy
    let t : T := ⟨x, hxT⟩
    have ht : t ∈ Subgroup.normalizer (P : Set T) := by
      intro y
      change y ∈ P ↔ t * y * t⁻¹ ∈ P
      rw [← mem_ambientSubgroup_iff P y, ← mem_ambientSubgroup_iff P (t * y * t⁻¹)]
      exact hxP y.val
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have htZ : t ∈ Subgroup.normalizer (Z : Set T) := by
      apply Subgroup.centralizer_le_normalizer
      apply Subgroup.mem_centralizer_iff.mpr
      intro z hz
      exact ((Subgroup.mem_center_iff.mp ((F.abelianCentralizerSystem_central E).in_center hz)) t).symm
    have htJ : t ∈ Subgroup.normalizer (J : Set T) :=
      Subgroup.normalizer_inf_normalizer_le_normalizer_sup P Z ⟨ht, htZ⟩
    have htA : t.val ∈ Subgroup.normalizer (A : Set S) :=
      Subgroup.le_normalizer_map T.subtype ⟨t, htJ, rfl⟩
    let b : (F.subgroupRestriction T).centralizingJoinAutomorphisms Z P :=
      ⟨J.normalizerMonoidHom ⟨t, htJ⟩,
        (F.subgroupRestriction T).normalizerAut_allowed J ⟨t, htJ⟩,
        (fun y => (ht y.val).symm), by
          intro z
          apply Subtype.ext
          change t.val * z.val.val * t.val⁻¹ = z.val.val
          have hc : z.val * t = t * z.val :=
            ((Subgroup.mem_center_iff.mp ((F.abelianCentralizerSystem_central E).in_center z.property)) t).symm
          have h := congrArg Subtype.val hc
          change z.val.val * t.val = t.val * z.val.val at h
          rw [← h, mul_assoc, mul_inv_cancel, mul_one]⟩
    apply (F.mem_kNormalizer_iff A K t.val).mpr
    refine ⟨htA, b, ?_⟩
    apply Subtype.ext
    ext y
    obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv T J).surjective y
    change (subgroupAmbientEquiv T J
      (b.val ((subgroupAmbientEquiv T J).symm ((subgroupAmbientEquiv T J) y)))).val = _
    rw [MulEquiv.symm_apply_apply]
    rfl

end Sharpness.FusionSystem
