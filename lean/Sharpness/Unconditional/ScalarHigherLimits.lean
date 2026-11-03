import Sharpness.Unconditional.CategoryBarCalculation
import Sharpness.HomologyFunctorTools

/-! Restriction of scalars commutes with the actual module-valued higher
limits in every degree. The comparison is assembled from the constructed
category bar resolution, the identical coefficient cochain formula, and
exactness of module scalar restriction. No field, flatness, finite-generation,
or finiteness-of-category hypothesis is required. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.Unconditional
open CategoryTheory Opposite Simplicial

variable {R B C : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Category.{u} C]

/-- In each degree the coefficient products have the identical underlying
R-module, before and after restricting scalars. -/
def scalarCoefficientCochainObjIso (D : CoefficientCategory B C) (n : ℕ) :
    (coefficientCochains (restrictCoefficientScalars (R := R) D)).X n ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj ((coefficientCochains D).X n) where
  hom := ModuleCat.ofHom
    (X := (coefficientCochains (restrictCoefficientScalars (R := R) D)).X n)
    (Y := (ModuleCat.restrictScalars (algebraMap R B)).obj ((coefficientCochains D).X n))
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  inv := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R B)).obj ((coefficientCochains D).X n))
    (Y := (coefficientCochains (restrictCoefficientScalars (R := R) D)).X n)
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The same signed sums of coefficient maps give an R-linear isomorphism
of the complete cochain complexes, including degree zero. -/
def scalarCoefficientCochainIso (D : CoefficientCategory B C) :
    coefficientCochains (restrictCoefficientScalars (R := R) D) ≅
      ((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (coefficientCochains D) :=
  HomologicalComplex.Hom.isoOfComponents (scalarCoefficientCochainObjIso D) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((coefficientCochains D).d i (i + 1)) x =
      ((coefficientCochains (restrictCoefficientScalars (R := R) D)).d i (i + 1)) x
    simp only [coefficientCochains, AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl)

/-- Scalar restriction commutes naturally with the constructed coefficient
cochain functor. -/
def scalarCoefficientCochainNatIso :
    scalarCoefficientFunctor R C B ⋙ coefficientCochainFunctor ≅
      coefficientCochainFunctor ⋙
        (ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex
          (ComplexShape.up ℕ) :=
  NatIso.ofComponents scalarCoefficientCochainIso (by
    intro D E f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- The actual native Ext higher limits commute with restriction of scalars,
naturally in all coefficient maps and for every n, including n = 0. -/
def scalarHigherLimitNatIso (n : ℕ) :
    higherLimitFunctor B C n ⋙ ModuleCat.restrictScalars (algebraMap R B) ≅
      scalarCoefficientFunctor R C B ⋙ higherLimitFunctor R C n :=
  Functor.isoWhiskerRight (categoryBarCohomologyNatIso (R := B) (C := C) n)
      (ModuleCat.restrictScalars (algebraMap R B)) ≪≫
    Functor.isoWhiskerLeft coefficientCochainFunctor
      (exactFunctorHomologyIso (c := ComplexShape.up ℕ) (i := n)
        (ModuleCat.restrictScalars (algebraMap R B))).symm ≪≫
    Functor.isoWhiskerRight scalarCoefficientCochainNatIso.symm
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n) ≪≫
    Functor.isoWhiskerLeft (scalarCoefficientFunctor R C B)
      (categoryBarCohomologyNatIso (R := R) (C := C) n).symm

/-- Objectwise R-module form of the all-degree scalar comparison. -/
def scalarHigherLimitIso (D : CoefficientCategory B C) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R B)).obj (higherLimit D n) ≅
      higherLimit (restrictCoefficientScalars (R := R) D) n :=
  (scalarHigherLimitNatIso (R := R) (B := B) (C := C) n).app D

omit [Algebra R B] in
/-- The manuscript's scalar comparison for an arbitrary homomorphism of
commutative rings, without an additional chosen algebra structure. -/
def scalarHigherLimitIsoOfRingHom (f : R →+* B)
    (D : CoefficientCategory B C) (n : ℕ) :
    (ModuleCat.restrictScalars f).obj (higherLimit D n) ≅
      higherLimit (D ⋙ ModuleCat.restrictScalars f) n := by
  letI : Algebra R B := f.toAlgebra
  exact scalarHigherLimitIso (R := R) D n

end Sharpness.Unconditional
