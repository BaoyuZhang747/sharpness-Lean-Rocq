import Sharpness.Unconditional.NormalizerOrbitCommaImageUniversal
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The pointed image subcategory is genuinely coreflective in the actual
normalizer orbit comma category. This is an explicit adjunction, not an input
asserting a comma-category homology comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def normalizerOrbitImageHomEquiv (P : F.CentricOrbit)
    (Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P) :
    ((F.normalizerOrbitPointedInclusion P).obj Y ⟶ X) ≃
      (Y ⟶ F.normalizerOrbitImagePoint P X) :=
  (Equiv.ofBijective
    (fun g : Y ⟶ F.normalizerOrbitImagePoint P X =>
      g.hom ≫ F.normalizerOrbitImageDeletion P X)
    ((Function.bijective_iff_existsUnique _).mpr (fun f => by
      obtain ⟨g, hg, hu⟩ := F.normalizerOrbitImage_universal P Y X f
      refine ⟨ObjectProperty.homMk g, hg, ?_⟩
      intro k hk
      apply ObjectProperty.hom_ext
      exact hu k.hom hk))).symm

theorem normalizerOrbitImageHomEquiv_naturality (P : F.CentricOrbit)
    (Y' Y : F.NormalizerOrbitPointed P) (X : F.NormalizerOrbitUnder P)
    (f : Y' ⟶ Y) (g : (F.normalizerOrbitPointedInclusion P).obj Y ⟶ X) :
    F.normalizerOrbitImageHomEquiv P Y' X
        ((F.normalizerOrbitPointedInclusion P).map f ≫ g) =
      f ≫ F.normalizerOrbitImageHomEquiv P Y X g := by
  apply (F.normalizerOrbitImageHomEquiv P Y' X).symm.injective
  rw [Equiv.symm_apply_apply]
  change f.hom ≫ g =
    (f.hom ≫ (F.normalizerOrbitImageHomEquiv P Y X g).hom) ≫
      F.normalizerOrbitImageDeletion P X
  rw [Category.assoc]
  exact congrArg (fun k => f.hom ≫ k)
    ((F.normalizerOrbitImageHomEquiv P Y X).symm_apply_apply g).symm

def normalizerOrbitImageCoreflection (P : F.CentricOrbit) :
    F.NormalizerOrbitUnder P ⥤ F.NormalizerOrbitPointed P :=
  Adjunction.rightAdjointOfEquiv (F.normalizerOrbitImageHomEquiv P)
    (F.normalizerOrbitImageHomEquiv_naturality P)

def normalizerOrbitImageCoreflectionAdjunction (P : F.CentricOrbit) :
    F.normalizerOrbitPointedInclusion P ⊣ F.normalizerOrbitImageCoreflection P :=
  Adjunction.adjunctionOfEquivRight (F.normalizerOrbitImageHomEquiv P)
    (F.normalizerOrbitImageHomEquiv_naturality P)

@[simp] theorem normalizerOrbitImageCoreflection_obj (P : F.CentricOrbit)
    (X : F.NormalizerOrbitUnder P) :
    (F.normalizerOrbitImageCoreflection P).obj X = F.normalizerOrbitImagePoint P X := rfl

theorem normalizerOrbitImageCoreflection_counit_app (P : F.CentricOrbit)
    (X : F.NormalizerOrbitUnder P) :
    (F.normalizerOrbitImageCoreflectionAdjunction P).counit.app X =
      F.normalizerOrbitImageDeletion P X :=
  F.normalizerOrbitPointed_source_hom_ext P (F.normalizerOrbitImagePoint P X) X _ _

end Sharpness.FusionSystem
