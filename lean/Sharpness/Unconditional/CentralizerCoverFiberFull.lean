import Sharpness.Unconditional.CentralizerCoverFiber

/-! Fullness of the native centralizer-to-cover-fiber functor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

instance localCentricToCoverFiber_full : (F.localCentricToCoverFiber p hS sat E C).Full where
  map_surjective {P Q} f := by
    let A := F.localCentricCoverObject p hS sat E C P
    let B := F.localCentricCoverObject p hS sat E C Q
    let q := F.centralizerCoverProjection p
    let T := F.centralizerGroup p E
    obtain ⟨g, hg, _⟩ := f.val.hom.property
    let g' : P.obj.as.subgroup →* Q.obj.as.subgroup :=
      (subgroupAmbientEquiv T Q.obj.as.subgroup).symm.toMonoidHom.comp
        (g.val.comp (subgroupAmbientEquiv T P.obj.as.subgroup).toMonoidHom)
    have hgg : ambientHom T g' = g.val := by
      ext x
      obtain ⟨x, rfl⟩ := (subgroupAmbientEquiv T P.obj.as.subgroup).surjective x
      rw [ambientHom_apply]
      exact congrArg Subtype.val
        ((subgroupAmbientEquiv T Q.obj.as.subgroup).apply_symm_apply (g.val _))
    have hP := F.elementaryInCentralizer_le_of_centric p hS sat E C P.obj.as.subgroup P.property
    have hlift : q.IsHomLift (𝟙 (op E)) f.val := f.property
    letI := hlift
    have hproj : q.map f.val = 𝟙 (op E) := by
      have hh := IsHomLift.fac' q (𝟙 (op E)) f.val
      rw [hh]
      apply Quiver.Hom.unop_inj
      apply InducedCategory.hom_ext
      apply Subtype.ext
      rfl
    have hinv : A.inverseRestriction B f.val.hom = 𝟙 (⟨E.obj.subgroup⟩ : F.Object) := by
      exact congrArg (fun h => h.unop.hom) hproj
    have hfix : ∀ z : F.elementaryInCentralizer p E,
        (g' ⟨z.val, hP z.property⟩).val = z.val := by
      intro z
      have hh := A.inverseRestriction_spec B f.val.hom g hg ⟨z.val.val, z.property⟩
      rw [hinv] at hh
      apply Subtype.ext
      change ((subgroupAmbientEquiv T Q.obj.as.subgroup).symm
        (g.val ((subgroupAmbientEquiv T P.obj.as.subgroup) ⟨z.val, hP z.property⟩))).val.val = z.val.val
      rw [subgroupAmbientEquiv_symm_val]
      exact hh
    have hg'C : C.system.IsHom g' := F.centralizer_hom_of_fixes_elementary
      p hS sat E C hP g' (hgg ▸ g.property) hfix
    let k : P ⟶ Q := ObjectProperty.homMk (C.system.toOrbit.map ⟨g', hg'C⟩)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply InducedCategory.hom_ext
    change F.toOrbit.map ⟨ambientHom T g', C.embedding.hom_mem g' hg'C⟩ = _
    have heq : (⟨ambientHom T g', C.embedding.hom_mem g' hg'C⟩ :
      A.centric.obj.as ⟶ B.centric.obj.as) = g := Subtype.ext hgg
    rw [heq]
    exact hg

end Sharpness.FusionSystem
