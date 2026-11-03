import Sharpness.Unconditional.NormalizerOrbitCommaImageObjects

/-! The actual image object satisfies the comma-category universal property.
The extension witness is transported through target-inner equivalence and
then restricted in codomain, preserving its literal selected chain images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

theorem normalizerOrbitPointed_source_hom_ext (P : F.CentricOrbit)
    (Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P)
    (f g : Y.obj ⟶ X) : f = g := by
  letI : IsIso Y.obj.hom := Y.property
  apply StructuredArrow.hom_ext
  apply NormalizerOrbitPair.hom_ext
  apply (cancel_epi Y.obj.hom).mp
  exact (StructuredArrow.w f).trans (StructuredArrow.w g).symm

def normalizerOrbitImageLift (P : F.CentricOrbit)
    (Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P)
    (f : Y.obj ⟶ X) : Y.obj ⟶ (F.normalizerOrbitImagePoint P X).obj := by
  letI : IsIso Y.obj.hom := Y.property
  let k : Y.obj.right.centric ⟶ F.normalizerOrbitArrowImage X.hom :=
    inv Y.obj.hom ≫ (F.normalizerOrbitArrowImageIso X.hom).hom
  have hk : k ≫ F.normalizerOrbitArrowImageInclusion X.hom = f.right.val := by
    apply (cancel_epi Y.obj.hom).mp
    dsimp [k]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    exact (F.normalizerOrbitArrowImage_factorization X.hom).trans (StructuredArrow.w f).symm
  let g := F.orbitRepresentative k.hom
  let g₀ := Classical.choose f.right.property
  have hg₀ := Classical.choose_spec f.right.property
  let a := Classical.choice hg₀.2
  have heq : F.toOrbit.map g₀ =
      F.toOrbit.map (g ≫ F.inclusion (F.arrowImage_le X.hom.hom)) := by
    rw [F.toOrbit.map_comp, F.orbitRepresentative_map]
    exact hg₀.1.trans (congrArg (fun q => q.hom) hk).symm
  let a' := a.ofOrbitEq X.right.normalizes heq
  let a'' := a'.changeCodomain g (fun _ => rfl)
  let h : Y.obj.right ⟶ F.normalizerOrbitImagePair P X :=
    NormalizerOrbitPair.homMk g a''
  have hh : h.val = k := by
    apply ObjectProperty.hom_ext
    exact F.orbitRepresentative_map k.hom
  exact StructuredArrow.homMk h (by
    change Y.obj.hom ≫ h.val = (F.normalizerOrbitArrowImageIso X.hom).hom
    rw [hh]
    change Y.obj.hom ≫ (inv Y.obj.hom ≫ _) = _
    rw [IsIso.hom_inv_id_assoc])

theorem normalizerOrbitImageLift_deletion (P : F.CentricOrbit)
    (Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P)
    (f : Y.obj ⟶ X) :
    F.normalizerOrbitImageLift P Y X f ≫ F.normalizerOrbitImageDeletion P X = f :=
  F.normalizerOrbitPointed_source_hom_ext P Y X _ _

theorem normalizerOrbitImage_universal (P : F.CentricOrbit)
    (Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P)
    (f : Y.obj ⟶ X) :
    ∃! g : Y.obj ⟶ (F.normalizerOrbitImagePoint P X).obj,
      g ≫ F.normalizerOrbitImageDeletion P X = f := by
  refine ⟨F.normalizerOrbitImageLift P Y X f,
    F.normalizerOrbitImageLift_deletion P Y X f, ?_⟩
  intro g _
  exact F.normalizerOrbitPointed_source_hom_ext P Y _ _ _

end Sharpness.FusionSystem
