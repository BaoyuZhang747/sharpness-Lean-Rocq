import Sharpness.V28.CentralizerDefinitions
import Sharpness.Unconditional.AbelianCentralizerSaturation

/-! Ambient transport of fixed-subgroup extensions, and agreement of general
centralizers with their abelian and elementary specializations. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.V28
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- Passing to the ambient group preserves subgroup joins. -/
theorem ambientSubgroup_sup (T : Subgroup S) (P Z : Subgroup T) :
    ambientSubgroup T (P ⊔ Z) = ambientSubgroup T P ⊔ ambientSubgroup T Z := by
  exact Subgroup.map_sup P Z T.subtype

/-- The fixed-subgroup extension condition commutes with the actual subgroup
embedding, on both the morphism and its extension over the join. -/
theorem centralizingHom_subgroupRestriction_iff
    (T : Subgroup S) (Z : Subgroup T) {P Q : Subgroup T} (f : P →* Q) :
    (F.subgroupRestriction T).CentralizingHom Z f ↔
      F.CentralizingHom (ambientSubgroup T Z) (ambientHom T f) := by
  unfold FusionSystem.CentralizingHom
  constructor
  · rintro ⟨hf, g, hg, hgP, hgZ⟩
    let pre := subgroupInclusion
      (ambientSubgroup T P ⊔ ambientSubgroup T Z) (ambientSubgroup T (P ⊔ Z))
      (ambientSubgroup_sup T P Z).ge
    let post := subgroupInclusion
      (ambientSubgroup T (Q ⊔ Z)) (ambientSubgroup T Q ⊔ ambientSubgroup T Z)
      (ambientSubgroup_sup T Q Z).le
    let gA := post.comp ((ambientHom T g).comp pre)
    refine ⟨hf, gA,
      F.comp_mem _ _ (F.comp_mem _ _ (F.inclusion_mem _) hg) (F.inclusion_mem _), ?_, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv T P).surjective x
      change (ambientHom T g (subgroupAmbientEquiv T (P ⊔ Z)
        ⟨y.val, Subgroup.mem_sup_left y.property⟩)).val =
        (ambientHom T f (subgroupAmbientEquiv T P y)).val
      rw [ambientHom_apply, ambientHom_apply]
      exact congrArg Subtype.val (hgP y)
    · intro z
      obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv T Z).surjective z
      change (ambientHom T g (subgroupAmbientEquiv T (P ⊔ Z)
        ⟨y.val, Subgroup.mem_sup_right y.property⟩)).val = y.val.val
      rw [ambientHom_apply]
      exact congrArg Subtype.val (hgZ y)
  · rintro ⟨hf, g, hg, hgP, hgZ⟩
    let pre := subgroupInclusion
      (ambientSubgroup T (P ⊔ Z)) (ambientSubgroup T P ⊔ ambientSubgroup T Z)
      (ambientSubgroup_sup T P Z).le
    let post := subgroupInclusion
      (ambientSubgroup T Q ⊔ ambientSubgroup T Z) (ambientSubgroup T (Q ⊔ Z))
      (ambientSubgroup_sup T Q Z).ge
    let gA := post.comp (g.comp pre)
    have hgA : F.IsHom gA :=
      F.comp_mem _ _ (F.comp_mem _ _ (F.inclusion_mem _) hg) (F.inclusion_mem _)
    let g' : (P ⊔ Z : Subgroup T) →* (Q ⊔ Z : Subgroup T) :=
      (subgroupAmbientEquiv T (Q ⊔ Z)).symm.toMonoidHom.comp
        (gA.comp (subgroupAmbientEquiv T (P ⊔ Z)).toMonoidHom)
    have heq : ambientHom T g' = gA := by
      apply MonoidHom.ext
      intro x
      change subgroupAmbientEquiv T (Q ⊔ Z)
        ((subgroupAmbientEquiv T (Q ⊔ Z)).symm
          (gA (subgroupAmbientEquiv T (P ⊔ Z)
            ((subgroupAmbientEquiv T (P ⊔ Z)).symm x)))) = gA x
      simp only [MulEquiv.apply_symm_apply]
    refine ⟨hf, g', ?_, ?_, ?_⟩
    · change F.IsHom (ambientHom T g')
      rw [heq]
      exact hgA
    · intro x
      apply Subtype.ext
      have hh := hgP (subgroupAmbientEquiv T P x)
      change (gA (subgroupAmbientEquiv T (P ⊔ Z)
        ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val =
        (ambientHom T f (subgroupAmbientEquiv T P x)).val at hh
      rw [← heq, ambientHom_apply, ambientHom_apply] at hh
      exact hh
    · intro z
      apply Subtype.ext
      have hh := hgZ (subgroupAmbientEquiv T Z z)
      change (gA (subgroupAmbientEquiv T (P ⊔ Z)
        ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val = z.val.val at hh
      rw [← heq, ambientHom_apply] at hh
      exact hh

/-- Fusion systems are equal when exactly the same actual homomorphisms are allowed. -/
theorem fusionSystem_ext (H K : FusionSystem S)
    (h : ∀ {P Q : Subgroup S} (f : P →* Q), H.IsHom f ↔ K.IsHom f) : H = K := by
  cases H
  cases K
  congr 1
  funext P Q f
  exact propext (h f)

/-- The general centralizer agrees with the internal construction for an abelian subgroup. -/
theorem centralizerOfSubgroup_abelian_eq (E : F.AbelianCentralizerData) :
    centralizerOfSubgroup F E.subgroup = F.abelianCentralizerSystem E := by
  apply fusionSystem_ext
  intro P Q f
  change F.CentralizingHom E.subgroup (ambientHom (F.abelianCentralizerGroup E) f) ↔
    (F.subgroupRestriction (F.abelianCentralizerGroup E)).CentralizingHom
      (F.abelianInCentralizer E) f
  simpa only [F.abelianInCentralizer_ambient E] using
    (centralizingHom_subgroupRestriction_iff F (F.abelianCentralizerGroup E)
      (F.abelianInCentralizer E) f).symm

/-- The general centralizer agrees with the elementary-subgroup construction. -/
theorem centralizerOfSubgroup_elementary_eq [Finite S] (p : ℕ)
    (E : F.ElementaryCategory p) :
    centralizerOfSubgroup F E.obj.subgroup = F.centralizerSystem p E := by
  apply fusionSystem_ext
  intro P Q f
  change F.CentralizingHom E.obj.subgroup (ambientHom (F.centralizerGroup p E) f) ↔
    (F.subgroupRestriction (F.centralizerGroup p E)).CentralizingHom
      (F.elementaryInCentralizer p E) f
  have he : ambientSubgroup (F.centralizerGroup p E) (F.elementaryInCentralizer p E) =
      E.obj.subgroup :=
    ambientSubgroup_subgroupOf _ _ (F.elementary_le_centralizer p E)
  simpa only [he] using
    (centralizingHom_subgroupRestriction_iff F (F.centralizerGroup p E)
      (F.elementaryInCentralizer p E) f).symm

/-- Fully centralized abelian subgroups have saturated general centralizers. -/
theorem centralizerOfSubgroup_saturated_of_abelian [Finite S]
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : Subgroup S) (hab : ∀ x y : E, x * y = y * x)
    (hE : F.FullyCentralized E) : (centralizerOfSubgroup F E).Saturated p := by
  rw [centralizerOfSubgroup_abelian_eq F ⟨E, hab⟩]
  exact F.abelianCentralizerSystem_saturated p hS sat ⟨E, hab⟩ hE

/-- An abelian subgroup is central in its general centralizer fusion system. -/
theorem centralizerOfSubgroup_central_of_abelian
    (E : Subgroup S) (hab : ∀ x y : E, x * y = y * x) :
    (centralizerOfSubgroup F E).CentralSubgroup
      (E.subgroupOf (Subgroup.centralizer (E : Set S))) := by
  rw [centralizerOfSubgroup_abelian_eq F ⟨E, hab⟩]
  exact F.abelianCentralizerSystem_central ⟨E, hab⟩

end Sharpness.FusionSystem.V28
