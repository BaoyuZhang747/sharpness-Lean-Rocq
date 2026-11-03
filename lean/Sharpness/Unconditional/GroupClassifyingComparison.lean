import Sharpness.Unconditional.CanonicalRealizationUnitInput
import Sharpness.CanonicalClassifyingComparison

/-! Unconditional comparison of the actual nerve-realized classifying space
with ordinary group cohomology, natural in groups and arbitrary modules. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable (R : Type u) [CommRing R] (G : Type u) [Group G] (A : ModuleCat.{u} R)

theorem canonicalClassifyingCochainMap_quasiIso_unconditional :
    QuasiIso (canonicalClassifyingCochainMap R G A) :=
  canonicalClassifyingCochainMap_quasiIso R G A (canonicalRealizationUnitInput R)

def groupClassifyingCohomologyIso (n : ℕ) :
    SingularCohomology.cohomology R (classifyingSpace G) A n ≅ value R G A n :=
  canonicalClassifyingIso R G A (canonicalRealizationUnitInput R) n

theorem groupClassifyingCohomologyIso_hom (n : ℕ) :
    (groupClassifyingCohomologyIso R G A n).hom =
      HomologicalComplex.homologyMap (canonicalClassifyingCochainMap R G A) n := rfl

variable {R G A}

theorem groupClassifyingCohomologyIso_coefficient {B : ModuleCat.{u} R}
    (a : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SingularCohomology.chainDualCoefficientMap R
          ((SingularCohomology.chainsFunctor R).obj (classifyingSpace G)) a) n ≫
        (groupClassifyingCohomologyIso R G B n).hom =
      (groupClassifyingCohomologyIso R G A n).hom ≫ coefficientMap G a n :=
  canonicalClassifyingIso_coefficient (canonicalRealizationUnitInput R) a n

theorem groupClassifyingCohomologyIso_group {H : Type u} [Group H]
    (f : G →* H) (n : ℕ) :
    SingularCohomology.pull R (classifyingMap f) A n ≫
        (groupClassifyingCohomologyIso R G A n).hom =
      (groupClassifyingCohomologyIso R H A n).hom ≫ pull (R := R) (A := A) f n :=
  canonicalClassifyingIso_group (canonicalRealizationUnitInput R) f n

def unconditionalClassifyingComparison (p : ℕ) [Fact p.Prime]
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) (n : ℕ) :
    ClassifyingComparisonInput p A n :=
  canonicalClassifyingComparison p (canonicalRealizationUnitInput (PrimeLocalRing.{u} p)) A n

theorem unconditionalClassifyingComparison_linearIso (p : ℕ) [Fact p.Prime]
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) (n : ℕ) (G : Type u) [Group G] :
    ((unconditionalClassifyingComparison p A n).linearIso G).hom =
      (groupClassifyingCohomologyIso (PrimeLocalRing.{u} p) G A n).hom :=
  canonicalClassifyingComparison_linearIso p (canonicalRealizationUnitInput _) A n G

end Sharpness.OrdinaryCohomology
