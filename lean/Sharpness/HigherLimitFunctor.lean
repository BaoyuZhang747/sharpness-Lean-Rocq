import Sharpness.ScalarBar

/-! The actual derived-limit functor in its coefficient variable, and
the actual restriction functors for the indexing category and scalars. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Opposite
variable (R : Type u) [CommRing R] (C : Type u) [Category.{u} C]

def higherLimitFunctor [EnoughProjectives (CoefficientCategory R C)] (n : ℕ) :
    CoefficientCategory R C ⥤ ModuleCat.{u} R :=
  (Ext R (CoefficientCategory R C) n).obj (op (constantCoefficient R C))

variable (k : Type u) [CommRing k] [Algebra R k]

def scalarCoefficientFunctor : CoefficientCategory k C ⥤ CoefficientCategory R C :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} k) (ModuleCat.{u} R)).obj
    (ModuleCat.restrictScalars (algebraMap R k))

variable {C} {D : Type u} [Category.{u} D]

def restrictionCoefficientFunctor (J : D ⥤ C) :
    CoefficientCategory R C ⥤ CoefficientCategory R D :=
  (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (ModuleCat.{u} R)).obj J.op

instance restrictionCoefficientFunctor_additive (J : D ⥤ C) :
    (restrictionCoefficientFunctor R J).Additive where
  map_add := by intros; rfl

instance restrictionCoefficientFunctor_linear (J : D ⥤ C) :
    (restrictionCoefficientFunctor R J).Linear R where
  map_smul := by intros; rfl

def scalarRestrictionCommute (J : D ⥤ C) :
    restrictionCoefficientFunctor k J ⋙ scalarCoefficientFunctor R D k ≅
      scalarCoefficientFunctor R C k ⋙ restrictionCoefficientFunctor R J := Iso.refl _

end Sharpness
