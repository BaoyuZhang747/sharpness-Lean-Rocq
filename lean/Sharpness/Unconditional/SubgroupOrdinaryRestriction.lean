import Sharpness.Unconditional.SubgroupCohomologyUnconditional
import Sharpness.LinkingSubgroupRestriction

/-! The actual restriction to native ordinary cohomology, with every
component fixed by its subgroup classifying map. No edge input is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (p : ℕ) [Fact p.Prime] (L : F.CentricLinkingSystem)
  (hS : IsPGroup p S) (sat : F.Saturated p)
  (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ)

def nativeOrdinaryRestrictionCone : Cone (F.cohomologyCoefficient (R := R) (A := A) n) where
  pt := SingularCohomology.cohomology R L.classifyingSpace A n
  π := (L.subgroupRestrictionCone R A n).π ≫
    (L.subgroupCohomologyCoefficientIso p R A n hS sat).hom

def nativeOrdinaryRestrictionToLimit :
    SingularCohomology.cohomology R L.classifyingSpace A n ⟶
      limit (F.cohomologyCoefficient (R := R) (A := A) n) :=
  limit.lift _ (L.nativeOrdinaryRestrictionCone p hS sat R A n)

theorem nativeOrdinaryRestrictionToLimit_component (P : F.CentricOrbit) :
    L.nativeOrdinaryRestrictionToLimit p hS sat R A n ≫
        limit.π (F.cohomologyCoefficient (R := R) (A := A) n) (op P) =
      SingularCohomology.pull R (L.subgroupClassifyingMap (L.linkingObjectOfOrbit P)) A n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n).hom := by
  rw [nativeOrdinaryRestrictionToLimit, limit.lift_π]
  change (SingularCohomology.pull R (L.subgroupDiagramForget P) A n ≫
      ((subgroupCohomologyComparison (L.canonicalBLOSubgroupComparisonInput p hS sat)
        R A (L.linkingObjectOfOrbit P) n).hom ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n).hom)) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫
      (OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n).hom)
      (subgroupComparison_restriction_component
        (L.canonicalBLOSubgroupComparisonInput p hS sat) R A (L.linkingObjectOfOrbit P) n))

theorem nativeOrdinaryRestrictionToLimit_eq :
    L.nativeOrdinaryRestrictionToLimit p hS sat R A n =
      L.subgroupRestrictionToLimit R A n ≫
        (HasLimit.isoOfNatIso (L.subgroupCohomologyCoefficientIso p R A n hS sat)).hom := by
  apply limit.hom_ext
  intro P
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    subgroupRestrictionToLimit_component]
  exact limit.lift_π _ _

theorem nativeOrdinaryRestrictionToLimit_isIso_of_subgroup
    [IsIso (L.subgroupRestrictionToLimit R A n)] :
    IsIso (L.nativeOrdinaryRestrictionToLimit p hS sat R A n) := by
  rw [nativeOrdinaryRestrictionToLimit_eq]
  infer_instance

end Sharpness.FusionSystem.CentricLinkingSystem
