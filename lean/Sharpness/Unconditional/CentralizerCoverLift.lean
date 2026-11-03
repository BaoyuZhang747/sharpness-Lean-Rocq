import Sharpness.Unconditional.CentralizerCoverProjection
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-! Lifts of elementary fusion morphisms through the centralizer cover. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

/-- Saturation lifts an elementary morphism oppositely to a cover arrow
whose underlying centric orbit arrow is an isomorphism. -/
theorem centralizerCover_exists_lift (sat : F.Saturated p)
    (A : F.CentralizedCentralizerCover p) (E : F.ElementaryCategory p)
    (θ : E ⟶ F.centralizedCoverElementary p A) :
    ∃ (B : F.CentralizedCentralizerCover p) (φ : A ⟶ B),
      (F.centralizerCoverProjection p).IsHomLift θ.op φ ∧ IsIso φ.hom.val := by
  let D := F.imageSubgroup θ.hom
  let e : E.obj.subgroup ≃* D := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective θ.hom.val θ.hom.property))
  have he : F.IsHom e.toMonoidHom := (F.toImage θ.hom).property
  have hPC : A.obj.centric.obj.as.subgroup ≤ Subgroup.centralizer (D : Set S) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp
      (A.obj.centralizes (F.image_le θ.hom hz))) x hx).symm
  obtain ⟨b, hb, hbE⟩ := F.centralizer_extension_of_fullyCentralized p sat
    e.symm (F.inverse_mem e he) E.property.2.2.2
  let g : A.obj.centric.obj.as.subgroup →* Subgroup.centralizer (E.obj.subgroup : Set S) :=
    b.comp (subgroupInclusion _ _ hPC)
  have hg : F.IsHom g := F.comp_mem _ _ (F.inclusion_mem hPC) hb
  let Q : Subgroup S := ((Subgroup.centralizer (E.obj.subgroup : Set S)).subtype.comp g).range
  let eP : A.obj.centric.obj.as.subgroup ≃* Q := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective g hg))
  have hQC : Q ≤ Subgroup.centralizer (E.obj.subgroup : Set S) := by
    rintro x ⟨a, rfl⟩
    exact (g a).property
  have heP : F.IsHom eP.toMonoidHom := by
    apply F.codomain_restrict_mem g hg hQC eP.toMonoidHom
    ext a
    rfl
  have hφθ : ∀ z : E.obj.subgroup,
      (eP ⟨(θ.hom.val z).val, A.obj.le_subgroup (θ.hom.val z).property⟩).val = z.val := by
    intro z
    have hh := hbE (e z) (hPC (A.obj.le_subgroup (θ.hom.val z).property))
    rw [MulEquiv.symm_apply_apply] at hh
    exact hh
  have hEQ : E.obj.subgroup ≤ Q := by
    intro z hz
    exact ⟨⟨(θ.hom.val ⟨z, hz⟩).val, A.obj.le_subgroup (θ.hom.val ⟨z, hz⟩).property⟩,
      hφθ ⟨z, hz⟩⟩
  let B₀ : F.CentralizerCover p :=
    { centric := ⟨F.toOrbit.obj ⟨Q⟩, F.isoSystem.centricIn_of_iso eP heP A.obj.centric.property⟩
      elementary := E.obj.subgroup
      nontrivial := E.property.1
      le_subgroup := hEQ
      centralizes := by
        intro z hz
        apply Subgroup.mem_centralizer_iff.mpr
        intro x hx
        exact ((Subgroup.mem_centralizer_iff.mp (hQC hx)) z hz).symm
      exponent := by
        intro z hz
        exact congrArg Subtype.val (E.property.2.2.1 ⟨z, hz⟩) }
  let B : F.CentralizedCentralizerCover p := ⟨B₀, E.property.2.2.2⟩
  let eC : A.obj.centric ≅ B₀.centric := ObjectProperty.isoMk _
    (F.toOrbit.mapIso (F.isoOfMulEquiv eP heP))
  let φ₀ : A.obj ⟶ B₀ :=
    ⟨eC.hom, ⟨eP.toMonoidHom, heP⟩, rfl, fun z => ⟨θ.hom.val z, hφθ z⟩⟩
  let φ : A ⟶ B := ObjectProperty.homMk φ₀
  have hq : (F.centralizerCoverProjection p).map φ = θ.op := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply MonoidHom.ext
    intro z
    exact A.obj.inverseRestriction_unique B₀ φ₀ z (θ.hom.val z)
      ⟨eP.toMonoidHom, heP⟩ rfl (hφθ z)
  refine ⟨B, φ, ?_, eC.isIso_hom⟩
  apply IsHomLift.of_fac' (F.centralizerCoverProjection p) θ.op φ rfl rfl
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hq

end Sharpness.FusionSystem
