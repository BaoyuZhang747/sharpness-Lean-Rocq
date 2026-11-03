import Sharpness.Unconditional.NormalizerOrbitExtensionRepresentatives
import Sharpness.FusionMinimal
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! The actual image object in the normalizer orbit comma category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

abbrev NormalizerOrbitUnder (P : F.CentricOrbit) :=
  StructuredArrow P F.normalizerOrbitPairForget

def normalizerOrbitPointedProperty (P : F.CentricOrbit) :
    ObjectProperty (F.NormalizerOrbitUnder P) := fun X => IsIso X.hom

abbrev NormalizerOrbitPointed (P : F.CentricOrbit) :=
  (F.normalizerOrbitPointedProperty P).FullSubcategory

def normalizerOrbitPointedInclusion (P : F.CentricOrbit) :
    F.NormalizerOrbitPointed P ⥤ F.NormalizerOrbitUnder P :=
  (F.normalizerOrbitPointedProperty P).ι

def normalizerOrbitArrowImage {P Q : F.CentricOrbit} (f : P ⟶ Q) : F.CentricOrbit := by
  let g := F.orbitRepresentative f.hom
  let g' : P.obj.as.subgroup →* S := Q.obj.as.subgroup.subtype.comp g.val
  let e := MonoidHom.ofInjective (f := g')
    (Subtype.val_injective.comp (F.injective _ g.property))
  refine ⟨F.toOrbit.obj ⟨F.arrowImage f.hom⟩, ?_⟩
  exact F.isoSystem.centricIn_of_iso e (F.toImage g).property P.property

def normalizerOrbitArrowImageIso {P Q : F.CentricOrbit} (f : P ⟶ Q) :
    P ≅ F.normalizerOrbitArrowImage f :=
  ObjectProperty.isoMk _ (F.arrowImageIso f.hom)

def normalizerOrbitArrowImageInclusion {P Q : F.CentricOrbit} (f : P ⟶ Q) :
    F.normalizerOrbitArrowImage f ⟶ Q :=
  ObjectProperty.homMk (F.arrowImageInclusion f.hom)

theorem normalizerOrbitArrowImage_factorization {P Q : F.CentricOrbit} (f : P ⟶ Q) :
    (F.normalizerOrbitArrowImageIso f).hom ≫ F.normalizerOrbitArrowImageInclusion f = f := by
  apply ObjectProperty.hom_ext
  exact F.arrow_factorization f.hom

def normalizerOrbitImagePair (P : F.CentricOrbit) (X : F.NormalizerOrbitUnder P) :
    F.NormalizerOrbitPair where
  centric := F.normalizerOrbitArrowImage X.hom
  chain := X.right.chain
  normalizes i := (F.arrowImage_le X.hom.hom).trans (X.right.normalizes i)

def normalizerOrbitImagePoint (P : F.CentricOrbit) (X : F.NormalizerOrbitUnder P) :
    F.NormalizerOrbitPointed P :=
  ⟨StructuredArrow.mk (Y := F.normalizerOrbitImagePair P X)
    (F.normalizerOrbitArrowImageIso X.hom).hom, by
      change IsIso (F.normalizerOrbitArrowImageIso X.hom).hom
      infer_instance⟩

def normalizerOrbitImagePairInclusion (P : F.CentricOrbit) (X : F.NormalizerOrbitUnder P) :
    F.normalizerOrbitImagePair P X ⟶ X.right :=
  NormalizerOrbitPair.homMk (F.inclusion (F.arrowImage_le X.hom.hom))
    (NormalizerChainExtension.inclusion (F.arrowImage_le X.hom.hom) X.right.chain)

def normalizerOrbitImageDeletion (P : F.CentricOrbit) (X : F.NormalizerOrbitUnder P) :
    (F.normalizerOrbitImagePoint P X).obj ⟶ X :=
  StructuredArrow.homMk (F.normalizerOrbitImagePairInclusion P X) (by
    change (F.normalizerOrbitArrowImageIso X.hom).hom ≫
      F.normalizerOrbitArrowImageInclusion X.hom = X.hom
    exact F.normalizerOrbitArrowImage_factorization X.hom)

end Sharpness.FusionSystem
