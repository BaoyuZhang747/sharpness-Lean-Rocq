import Sharpness.GroupNerveCochainNaturality
import Sharpness.RealizationUnitCochainNaturality
import Sharpness.GroupClassifyingCohomologyInput

/-! A specified classifying-space comparison obtained from the actual
realization unit and the proved nerve/inhomogeneous cochain isomorphism.
Its naturality in coefficients and groups is proved at cochain level.
The only external input is the previously recorded uniform realization
unit chain quasi-isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable (R : Type u) [CommRing R] (G : Type u) [Group G] (A : ModuleCat.{u} R)

def canonicalClassifyingCochainMap :
    SingularCohomology.cochains R (classifyingSpace G) A ⟶
      groupCohomology.inhomogeneousCochains (Rep.trivial R G A) :=
  realizationUnitCochainMap R (nerve (SingleObj G)) A ≫ (nerveCochainIso R G A).hom

theorem canonicalClassifyingCochainMap_quasiIso (real : RealizationUnitInput.{u} R) :
    QuasiIso (canonicalClassifyingCochainMap R G A) := by
  letI := realizationUnitCochainMap_quasiIso R (nerve (SingleObj G)) A real
  dsimp only [canonicalClassifyingCochainMap, classifyingSpace]
  infer_instance

variable {R G A}

theorem canonicalClassifyingCochainMap_coefficient {B : ModuleCat.{u} R} (a : A ⟶ B) :
    SingularCohomology.chainDualCoefficientMap R
        ((SingularCohomology.chainsFunctor R).obj (classifyingSpace G)) a ≫
        canonicalClassifyingCochainMap R G B =
      canonicalClassifyingCochainMap R G A ≫ coefficientCochainMap G a := by
  dsimp only [canonicalClassifyingCochainMap, classifyingSpace]
  rw [← Category.assoc, realizationUnitCochainMap_coefficient, Category.assoc,
    nerveCochainIso_coefficient, ← Category.assoc]

theorem canonicalClassifyingCochainMap_group {H : Type u} [Group H] (f : G →* H) :
    SingularCohomology.cochainPull R (classifyingMap f) A ≫
        canonicalClassifyingCochainMap R G A =
      canonicalClassifyingCochainMap R H A ≫ cochainPull (R := R) (A := A) f := by
  dsimp only [canonicalClassifyingCochainMap, classifyingMap]
  rw [← Category.assoc, realizationUnitCochainMap_naturality, Category.assoc,
    nerveCochainIso_group, ← Category.assoc]

variable (R G A)

def canonicalClassifyingIso (real : RealizationUnitInput.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R (classifyingSpace G) A n ≅ value R G A n := by
  letI := canonicalClassifyingCochainMap_quasiIso R G A real
  exact asIso (HomologicalComplex.homologyMap (canonicalClassifyingCochainMap R G A) n)

theorem canonicalClassifyingIso_hom (real : RealizationUnitInput.{u} R) (n : ℕ) :
    (canonicalClassifyingIso R G A real n).hom =
      HomologicalComplex.homologyMap (canonicalClassifyingCochainMap R G A) n := rfl

variable {R G A}

theorem canonicalClassifyingIso_coefficient (real : RealizationUnitInput.{u} R)
    {B : ModuleCat.{u} R} (a : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SingularCohomology.chainDualCoefficientMap R
          ((SingularCohomology.chainsFunctor R).obj (classifyingSpace G)) a) n ≫
        (canonicalClassifyingIso R G B real n).hom =
      (canonicalClassifyingIso R G A real n).hom ≫ coefficientMap G a n := by
  simp only [canonicalClassifyingIso_hom, coefficientMap,
    ← HomologicalComplex.homologyMap_comp, canonicalClassifyingCochainMap_coefficient]

theorem canonicalClassifyingIso_group (real : RealizationUnitInput.{u} R)
    {H : Type u} [Group H] (f : G →* H) (n : ℕ) :
    SingularCohomology.pull R (classifyingMap f) A n ≫
        (canonicalClassifyingIso R G A real n).hom =
      (canonicalClassifyingIso R H A real n).hom ≫ pull (R := R) (A := A) f n := by
  simp only [canonicalClassifyingIso_hom, SingularCohomology.pull, pull,
    ← HomologicalComplex.homologyMap_comp, canonicalClassifyingCochainMap_group]

end Sharpness.OrdinaryCohomology
