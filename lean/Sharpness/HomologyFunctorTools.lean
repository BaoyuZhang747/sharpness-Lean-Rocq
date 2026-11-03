import Mathlib
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! Linearity and exact-functor comparison for actual complex homology.
These follow from the native short-complex homology construction. -/
set_option autoImplicit false
noncomputable section
universe u v w t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R] {C : Type v} [Category.{u} C] [Abelian C]
    [CategoryTheory.Linear R C] {ι : Type t} (c : ComplexShape ι) (i : ι)

set_option backward.isDefEq.respectTransparency false in
theorem homologicalComplex_homologyMap_smul {K L : HomologicalComplex C c}
    (f : K ⟶ L) (a : R) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  dsimp [HomologicalComplex.homologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

instance homologicalComplex_homologyFunctor_linear :
    (HomologicalComplex.homologyFunctor C c i).Linear R where
  map_smul f a := homologicalComplex_homologyMap_smul R c i f a

variable {D : Type w} [Category.{u} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

def exactFunctorHomologyIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c i).map f) F)

end Sharpness
