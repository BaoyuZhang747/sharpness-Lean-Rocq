import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Absolute-to-relative cohomology for an actual mapping cone.
If the source cohomology vanishes in degrees n and n+1, the actual
right inclusion induces an isomorphism. The proof uses the two native
exact sequences of the distinguished mapping-cone triangle. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) (n : ℤ)

theorem mappingConeInr_homologyMap_isIso
    (hn : IsZero (A.homology n)) (hn' : IsZero (A.homology (n+1))) :
    IsIso (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n) := by
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  let T := CochainComplex.mappingCone.triangleh f
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  have hz : IsZero ((H.shift n).obj T.obj₁) :=
    IsZero.of_iso hn ((HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app A)
  have hz' : IsZero ((H.shift (n+1)).obj T.obj₁) :=
    IsZero.of_iso hn' ((HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) (n+1)).app A)
  letI : Mono ((H.shift n).map T.mor₂) :=
    (H.homologySequence_exact₂ T hT n).mono_g_iff.mpr (hz.eq_of_src _ _)
  letI : Epi ((H.shift n).map T.mor₂) :=
    (H.homologySequence_exact₃ T hT n (n+1) rfl).epi_f_iff.mpr (hz'.eq_of_tgt _ _)
  letI : IsIso ((H.shift n).map T.mor₂) := isIso_of_mono_of_epi _
  have he := (HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u} R) (ComplexShape.up ℤ) n).hom.naturality (CochainComplex.mappingCone.inr f)
  haveI : IsIso ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
      ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f))) :=
    inferInstanceAs (IsIso ((H.shift n).map T.mor₂))
  have hi : IsIso (((HomotopyCategory.homologyFunctorFactors
        (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app B).hom ≫
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n) := by
    exact he ▸ (inferInstance : IsIso
      ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) ≫
          ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app
            (CochainComplex.mappingCone f)).hom))
  letI := hi
  exact IsIso.of_isIso_comp_left ((HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app B).hom _

def mappingConeInrCohomologyIso
    (hn : IsZero (A.homology n)) (hn' : IsZero (A.homology (n+1))) :
    B.homology n ≅ (CochainComplex.mappingCone f).homology n := by
  letI := mappingConeInr_homologyMap_isIso f n hn hn'
  exact asIso (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n)

def mappingConeAbsoluteMap : B.homology n ⟶
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone f)) :=
  HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n ≫
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R)
      (ComplexShape.up ℤ) n).app (CochainComplex.mappingCone f)).inv

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeAbsoluteMap_naturality
    {A' B' : CochainComplex (ModuleCat.{u} R) ℤ} (f' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (comm : f ≫ b = a ≫ f') :
    HomologicalComplex.homologyMap b n ≫ mappingConeAbsoluteMap f' n =
      mappingConeAbsoluteMap f n ≫
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
          ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.map f f' a b comm)) := by
  have hc := congrArg (fun t => HomologicalComplex.homologyMap t n)
    (CochainComplex.mappingCone.triangleMap f f' a b comm).comm₂
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have hf := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R)
    (ComplexShape.up ℤ) n).inv.naturality (CochainComplex.mappingCone.map f f' a b comm)
  calc
    _ = (HomologicalComplex.homologyMap b n ≫
        HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f') n) ≫
          ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R)
            (ComplexShape.up ℤ) n).app (CochainComplex.mappingCone f')).inv :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n ≫
        HomologicalComplex.homologyMap (CochainComplex.mappingCone.map f f' a b comm) n) ≫ _ :=
      congrArg (fun t => t ≫ ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R)
        (ComplexShape.up ℤ) n).app (CochainComplex.mappingCone f')).inv) hc.symm
    _ = HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n ≫
        (HomologicalComplex.homologyMap (CochainComplex.mappingCone.map f f' a b comm) n ≫ _) :=
      Category.assoc _ _ _
    _ = _ := (congrArg (fun t => HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr f) n ≫ t) hf).trans (Category.assoc _ _ _).symm

end Sharpness
