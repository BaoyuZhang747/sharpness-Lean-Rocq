import Sharpness.Unconditional.GroupCohomologySubgroupTransferTower
import Sharpness.Unconditional.GroupCohomologyTransferResolution
import Sharpness.Unconditional.GroupCohomologyNestedPull

/-! Native subgroup transfer is computed by the same ambient bar resolution
for every subgroup. The actual cochain tower identity therefore gives
transitivity on ordinary group cohomology in every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G A : Type u} [CommRing R] [Group G]
    [AddCommGroup A] [Module R A]

/-- The literal subgroup cochain transfer factors through the canonical
nested subgroup type and native Hom transfer there. -/
theorem subgroupHomComplexTransfer_factor (P Q : Subgroup G) (h : P ≤ Q)
    [(P.subgroupOf Q).FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    subgroupHomComplexToNested P Q h X V ≫
        homComplexTransfer (P.subgroupOf Q)
          (((Rep.resFunctor Q.subtype).mapHomologicalComplex _).obj X)
          (Rep.res Q.subtype V) =
      subgroupHomComplexTransfer P Q h X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rfl

/-- The native ordinary-cohomology transfer agrees with the actual transfer
on the common ambient bar Hom complex. -/
theorem subgroupTransfer_ambient_comparison [Finite G]
    (P Q : Subgroup G) (h : P ≤ Q) (n : ℕ) :
    ModuleCat.ofHom (subgroupTransfer (R := R) (A := A) P Q h n) ≫
        (ambientBarCohomologyIso Q (Rep.trivial R G A) n).hom =
      (ambientBarCohomologyIso P (Rep.trivial R G A) n).hom ≫
        HomologicalComplex.homologyMap
          (subgroupHomComplexTransfer P Q h (Rep.barResolution R G).complex
            (Rep.trivial R G A)) n := by
  change (pull (R := R) (A := A) (Subgroup.subgroupOfEquivOfLe h).toMonoidHom n ≫
    corestriction (P.subgroupOf Q) (Rep.trivial R Q A) n) ≫ _ = _
  have hc := corestriction_resolution_comparison (P.subgroupOf Q)
    (ambientBarResolution (R := R) Q) (Rep.trivial R Q A) n
  change corestriction (P.subgroupOf Q) (Rep.trivial R Q A) n ≫
      (ambientBarCohomologyIso Q (Rep.trivial R G A) n).hom =
    (groupCohomologyIso (Rep.trivial R (P.subgroupOf Q) A) n
      (nestedBarResolution P Q)).hom ≫
      HomologicalComplex.homologyMap
        (homComplexTransfer (P.subgroupOf Q) (ambientBarResolution (R := R) Q).complex
          (Rep.trivial R Q A)) n at hc
  rw [Category.assoc, hc,
    ← Category.assoc, subgroupOfEquiv_pull_comparison,
    Category.assoc, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun f =>
    (ambientBarCohomologyIso P (Rep.trivial R G A) n).hom ≫
      HomologicalComplex.homologyMap f n)
    (subgroupHomComplexTransfer_factor P Q h (Rep.barResolution R G).complex
      (Rep.trivial R G A))

/-- Ordinary group-cohomology transfer is transitive for literal subgroup
inclusions, with arbitrary trivial module coefficients and all degrees. -/
theorem subgroupTransfer_comp [Finite G]
    (P Q T : Subgroup G) (hPQ : P ≤ Q) (hQT : Q ≤ T) (n : ℕ) :
    (subgroupTransfer (R := R) (A := A) Q T hQT n).comp
        (subgroupTransfer (R := R) (A := A) P Q hPQ n) =
      subgroupTransfer (R := R) (A := A) P T (hPQ.trans hQT) n := by
  have hc :
      ModuleCat.ofHom (subgroupTransfer (R := R) (A := A) P Q hPQ n) ≫
          ModuleCat.ofHom (subgroupTransfer (R := R) (A := A) Q T hQT n) =
        ModuleCat.ofHom (subgroupTransfer (R := R) (A := A) P T (hPQ.trans hQT) n) := by
    apply (cancel_mono (ambientBarCohomologyIso T (Rep.trivial R G A) n).hom).mp
    rw [Category.assoc, subgroupTransfer_ambient_comparison,
      ← Category.assoc, subgroupTransfer_ambient_comparison,
      Category.assoc, ← HomologicalComplex.homologyMap_comp,
      subgroupHomComplexTransfer_comp, subgroupTransfer_ambient_comparison]
  exact congrArg (fun f : value R P A n ⟶ value R T A n => f.hom) hc

end Sharpness.OrdinaryCohomology
