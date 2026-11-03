import Sharpness.Unconditional.NormalizerOrbitPointedSingleton

/-! The actual undercategories for first-entry evaluation and their full
subcategories with invertible structural arrows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S) (P : F.CentricOrbit)

abbrev NormalizerPointedFirstUnder (A : F.NormalizerPointedSubgroup P) :=
  StructuredArrow A (F.normalizerOrbitPointedFirst P)

def normalizerPointedFirstIsoProperty (A : F.NormalizerPointedSubgroup P) :
    ObjectProperty (F.NormalizerPointedFirstUnder P A) := fun X => IsIso X.hom

abbrev NormalizerPointedFirstIso (A : F.NormalizerPointedSubgroup P) :=
  (F.normalizerPointedFirstIsoProperty P A).FullSubcategory

def normalizerPointedFirstIsoInclusion (A : F.NormalizerPointedSubgroup P) :
    F.NormalizerPointedFirstIso P A ⥤ F.NormalizerPointedFirstUnder P A :=
  (F.normalizerPointedFirstIsoProperty P A).ι

instance normalizerPointedFirstUnder_homSubsingleton (A : F.NormalizerPointedSubgroup P)
    (X Y : F.NormalizerPointedFirstUnder P A) : Subsingleton (X ⟶ Y) := by
  letI : Subsingleton (X.right ⟶ Y.right) := F.normalizerOrbitPointedHom_subsingleton P _ _
  constructor
  intro f g
  apply StructuredArrow.hom_ext
  exact Subsingleton.elim _ _

def normalizerPointedFirstIsoBase (A : F.NormalizerPointedSubgroup P) :
    F.NormalizerPointedFirstIso P A :=
  ⟨F.normalizerOrbitPointedFirstBase P A,by
    change IsIso (eqToHom (F.normalizerOrbitPointedFirst_singleton P A).symm)
    infer_instance⟩

end Sharpness.FusionSystem
