import Sharpness.CanonicalClassifyingCochains

/-! The proved, coefficient-natural comparison supplies the earlier
fixed-coefficient reference interface. The equality of its actual
linear map with the canonical cochain-induced map is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable (p : ℕ) [Fact p.Prime]
    (real : RealizationUnitInput.{u} (PrimeLocalRing.{u} p))
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) (n : ℕ)

def canonicalClassifyingComparison : ClassifyingComparisonInput p A n where
  AKO_III_1_7 G := (canonicalClassifyingIso (PrimeLocalRing.{u} p) G A real n).toLinearEquiv.toAddEquiv
  naturality {G H} _ _ f x := by
    exact congrArg (fun t => t x) (canonicalClassifyingIso_group real f n)

theorem canonicalClassifyingComparison_linearIso (G : Type u) [Group G] :
    ((canonicalClassifyingComparison p real A n).linearIso G).hom =
      (canonicalClassifyingIso (PrimeLocalRing.{u} p) G A real n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem canonicalClassifyingComparison_coefficient {B : ModuleCat.{u} (PrimeLocalRing.{u} p)}
    (a : A ⟶ B) (G : Type u) [Group G] :
    HomologicalComplex.homologyMap
        (SingularCohomology.chainDualCoefficientMap (PrimeLocalRing.{u} p)
          ((SingularCohomology.chainsFunctor (PrimeLocalRing.{u} p)).obj (classifyingSpace G)) a) n ≫
        ((canonicalClassifyingComparison p real B n).linearIso G).hom =
      ((canonicalClassifyingComparison p real A n).linearIso G).hom ≫ coefficientMap G a n := by
  rw [canonicalClassifyingComparison_linearIso, canonicalClassifyingComparison_linearIso]
  exact canonicalClassifyingIso_coefficient real a n

end Sharpness.OrdinaryCohomology
