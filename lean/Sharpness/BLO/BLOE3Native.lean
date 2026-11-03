import Sharpness.BLO.BLOE3Cohomology
import Sharpness.BLO.BLOCohomologyComparison

/-!
The actual enlarged-linking native cohomology diagram has the ambient
cohomology higher limits in every degree. Its natural coefficient comparison
is constructed from distinguished group restrictions, with all arrow squares
proved in `BLOCohomologyComparison`. The E3 comparison used here applies the
Task 1 cohomology corollary to actual centraliser systems and to the ambient
system. No coefficient-comparison or sharpness hypothesis remains.

The coefficient is covariant on `F.ElementaryCategory p`; only positive
derived degrees vanish. The ordinary limit is retained in the all-degree
comparison and in the separate canonical edge theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] [Nontrivial S]
    {F : FusionSystem S} (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

/-- The actual native BLO diagram and ambient cohomology coefficient have
isomorphic derived limits in every nonnegative degree. -/
def BLOCohomologyHigherLimitIso (n s : ℕ) :
    covariantHigherLimit (PrimeField.{u} p) (L.BLOCohomologyDiagram p n) s ≅
      higherLimit (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s :=
  BLO.cohomologyHigherLimitIso_of_natIso p F hS sat n
    (L.BLOCohomologyRightKanIso p hS sat n) s

include hS sat in
/-- Every positive derived limit of the actual covariant native BLO
cohomology diagram vanishes, for arbitrary cohomological degree `n`. -/
theorem BLOCohomologyPositiveIsZero (n s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p)
      (L.BLOCohomologyDiagram p n) s) :=
  BLO.cohomology_positive_isZero_of_natIso p F hS sat n
    (L.BLOCohomologyRightKanIso p hS sat n) s hs

end Sharpness.FusionSystem.CentricLinkingSystem
