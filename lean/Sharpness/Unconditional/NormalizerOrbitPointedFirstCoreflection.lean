import Sharpness.Unconditional.NormalizerOrbitPointedFirstTerminal

/-! The actual image-prefix coreflection in the first-entry comma category.
The prefix is inserted precisely when the image is a proper subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
  (P : F.CentricOrbit) (A : F.NormalizerPointedSubgroup P)

structure NormalizerPointedFirstCoreflectionData (X : F.NormalizerPointedFirstUnder P A) where
  point : F.NormalizerPointedFirstIso P A
  deletion : point.obj ⟶ X
  lift : ∀ (Y : F.NormalizerPointedFirstIso P A), (Y.obj ⟶ X) → (Y ⟶ point)

def normalizerPointedFirstCoreflectionData (X : F.NormalizerPointedFirstUnder P A) :
    F.NormalizerPointedFirstCoreflectionData P A X := Classical.choice (by
  classical
  by_cases he : NormalizerPointedSubgroup.arrowImage X.hom = X.right.obj.right.chain.subgroup 0
  · letI : IsIso X.hom := NormalizerPointedSubgroup.isIso_of_arrowImage_eq_target X.hom he
    exact ⟨⟨⟨X,show IsIso X.hom from inferInstance⟩,𝟙 X,fun _ f => ObjectProperty.homMk f⟩⟩
  · let B := NormalizerPointedSubgroup.imageObject X.hom
    let I : F.CentricSubgroup := ⟨B.subgroup,B.subgroup_centric⟩
    have hI : I.val < X.right.obj.right.chain.subgroup 0 :=
      lt_of_le_of_ne (NormalizerPointedSubgroup.arrowImage_le X.hom) he
    let Z := F.normalizerOrbitPointedPrepend P X.right I hI B.normalizes
    have hfirst : (F.normalizerOrbitPointedFirst P).obj Z = B := rfl
    let e : A ≅ (F.normalizerOrbitPointedFirst P).obj Z :=
      NormalizerPointedSubgroup.imageIso X.hom ≪≫ eqToIso hfirst.symm
    let U : F.NormalizerPointedFirstIso P A :=
      ⟨StructuredArrow.mk e.hom,e.isIso_hom⟩
    let deletion : U.obj ⟶ X := StructuredArrow.homMk
      (F.normalizerOrbitPointedPrependDeletion P X.right I hI B.normalizes)
      (Subsingleton.elim _ _)
    refine ⟨⟨U,deletion,fun Y f => Classical.choice ?_⟩⟩
    obtain ⟨g,hg,⟨a⟩⟩ := f.right.hom.right.property
    have hImage := F.normalizerPointedFirst_under_carrier_image p hS sat P Y X f g hg a
    let k := F.normalizerOrbitPointedPrependLift P f.right I hI B.normalizes g hg a hImage
    exact ⟨ObjectProperty.homMk (StructuredArrow.homMk k (Subsingleton.elim _ _))⟩)

def normalizerPointedFirstHomEquiv (Y : F.NormalizerPointedFirstIso P A)
    (X : F.NormalizerPointedFirstUnder P A) :
    ((F.normalizerPointedFirstIsoInclusion P A).obj Y ⟶ X) ≃
      (Y ⟶ (F.normalizerPointedFirstCoreflectionData p hS sat P A X).point) where
  toFun := (F.normalizerPointedFirstCoreflectionData p hS sat P A X).lift Y
  invFun f := f.hom ≫ (F.normalizerPointedFirstCoreflectionData p hS sat P A X).deletion
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by apply ObjectProperty.hom_ext; exact Subsingleton.elim _ _

theorem normalizerPointedFirstHomEquiv_naturality
    (Y' Y : F.NormalizerPointedFirstIso P A) (X : F.NormalizerPointedFirstUnder P A)
    (f : Y' ⟶ Y) (g : (F.normalizerPointedFirstIsoInclusion P A).obj Y ⟶ X) :
    F.normalizerPointedFirstHomEquiv p hS sat P A Y' X
        ((F.normalizerPointedFirstIsoInclusion P A).map f ≫ g) =
      f ≫ F.normalizerPointedFirstHomEquiv p hS sat P A Y X g := by
  apply ObjectProperty.hom_ext
  exact Subsingleton.elim _ _

def normalizerPointedFirstCoreflection :
    F.NormalizerPointedFirstUnder P A ⥤ F.NormalizerPointedFirstIso P A :=
  Adjunction.rightAdjointOfEquiv (F.normalizerPointedFirstHomEquiv p hS sat P A)
    (F.normalizerPointedFirstHomEquiv_naturality p hS sat P A)

def normalizerPointedFirstCoreflectionAdjunction :
    F.normalizerPointedFirstIsoInclusion P A ⊣ F.normalizerPointedFirstCoreflection p hS sat P A :=
  Adjunction.adjunctionOfEquivRight (F.normalizerPointedFirstHomEquiv p hS sat P A)
    (F.normalizerPointedFirstHomEquiv_naturality p hS sat P A)

end Sharpness.FusionSystem
