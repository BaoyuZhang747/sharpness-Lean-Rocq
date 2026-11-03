import Sharpness.LinkingOrbitLifts
import Sharpness.LinkingSubgroupCochains
import Sharpness.Unconditional.CanonicalBLOComparison
import Sharpness.Unconditional.GroupClassifyingComparison
import Sharpness.Manuscript.CohomologyUnconditional
import Sharpness.Unconditional.LocalSharpness

/-! Actual subgroup-space coefficients are naturally native group cohomology,
for arbitrary commutative rings and trivial modules. The coefficient
comparison and subsequent vanishing have all former inputs constructed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (p : ℕ) [Fact p.Prime] (L : F.CentricLinkingSystem)
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (BLO : L.BLOSubgroupComparisonInput p hS sat)
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ)

def nativeSubgroupCoefficientComparisonComponent (P : F.CentricOrbit) :
    (L.subgroupCohomologyDiagram R A n).obj (op P) ≅
      (F.cohomologyCoefficient (R := R) (A := A) n).obj (op P) :=
  (subgroupCohomologyComparison BLO R A
    (L.linkingObjectOfOrbit P) n) ≪≫ OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n

set_option backward.isDefEq.respectTransparency false in
theorem nativeSubgroupCoefficientComparison_naturality {P Q : F.CentricOrbit} (a : P ⟶ Q) :
    (L.subgroupCohomologyDiagram R A n).map a.op ≫
        (L.nativeSubgroupCoefficientComparisonComponent p BLO R A n P).hom =
      (L.nativeSubgroupCoefficientComparisonComponent p BLO R A n Q).hom ≫
        (F.cohomologyCoefficient (R := R) (A := A) n).map a.op := by
  let f := L.liftOrbitArrow a
  have h₁ := subgroupCohomologyComparison_naturality BLO R A f n
  have h₂ := OrdinaryCohomology.groupClassifyingCohomologyIso_group (R := R) (A := A) (L.projection.map f).val n
  have h₃ : (F.cohomologyCoefficient (R := R) (A := A) n).map a.op =
      OrdinaryCohomology.pull (R := R) (A := A)
        (L.projection.map f).val n := by
    change ModuleCat.ofHom (F.groupCohomologyOrbitPull a.hom) = _
    have hf := L.projection_liftOrbitArrow a
    exact congrArg (fun g : P.obj.as ⟶ Q.obj.as => OrdinaryCohomology.pull (R := R)
      (A := A) g.val n) hf.symm
  have h₄ : L.orbitProjection.map f = a := L.orbitProjection_liftOrbitArrow a
  rw [h₄] at h₁
  change SingularCohomology.pull R (L.subgroupDiagram.map a) A n ≫
      ((subgroupCohomologyComparison BLO R A
          (L.linkingObjectOfOrbit P) n).hom ≫ (OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n).hom) =
    ((subgroupCohomologyComparison BLO R A
        (L.linkingObjectOfOrbit Q) n).hom ≫ (OrdinaryCohomology.groupClassifyingCohomologyIso R Q.obj.as.subgroup A n).hom) ≫ _
  let cP := (subgroupCohomologyComparison BLO R A
    (L.linkingObjectOfOrbit P) n).hom
  let cQ := (subgroupCohomologyComparison BLO R A
    (L.linkingObjectOfOrbit Q) n).hom
  let bP := (OrdinaryCohomology.groupClassifyingCohomologyIso R P.obj.as.subgroup A n).hom
  let bQ := (OrdinaryCohomology.groupClassifyingCohomologyIso R Q.obj.as.subgroup A n).hom
  let v := SingularCohomology.pull R (L.classifyingMapOfProjection f) A n
  let w := OrdinaryCohomology.pull (R := R) (A := A)
    (L.projection.map f).val n
  calc
    _ = (SingularCohomology.pull R (L.subgroupDiagram.map a) A n ≫
        cP) ≫ bP := (Category.assoc _ _ _).symm
    _ = (cQ ≫ v) ≫ bP := congrArg (fun t => t ≫ bP) h₁
    _ = cQ ≫ (v ≫ bP) := Category.assoc _ _ _
    _ = cQ ≫ (bQ ≫ w) := congrArg (fun t => cQ ≫ t) h₂
    _ = (cQ ≫ bQ) ≫ w := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun t => (cQ ≫ bQ) ≫ t) h₃.symm

def nativeSubgroupCoefficientIso : L.subgroupCohomologyDiagram R A n ≅
    F.cohomologyCoefficient (R := R) (A := A) n :=
  NatIso.ofComponents (fun P => L.nativeSubgroupCoefficientComparisonComponent p BLO R A n P.unop)
    (fun a => L.nativeSubgroupCoefficientComparison_naturality p BLO R A n a.unop)



/-- Unconditional natural comparison for the actual subgroup decomposition. -/
def subgroupCohomologyCoefficientIso (hS : IsPGroup p S) (sat : F.Saturated p) :
    L.subgroupCohomologyDiagram R A n ≅ F.cohomologyCoefficient (R := R) (A := A) n :=
  L.nativeSubgroupCoefficientIso p (L.canonicalBLOSubgroupComparisonInput p hS sat) R A n

/-- Field-valued subgroup decomposition coefficients have vanishing positive
higher limits, for arbitrary trivial module values. -/
theorem subgroupCohomology_acyclic_unconditional (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ) :
    Acyclic (L.subgroupCohomologyDiagram k A n) :=
  acyclic_of_iso (L.subgroupCohomologyCoefficientIso p k A n hS sat)
    (F.cohomology_acyclic_unconditional p k hS sat n)

/-- The same actual diagram is acyclic for every trivial localized-integer module. -/
theorem subgroupCohomology_primeLocal_acyclic_unconditional
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) (n : ℕ) :
    Acyclic (L.subgroupCohomologyDiagram (PrimeLocalRing.{u} p) A n) := by
  apply acyclic_of_iso (L.subgroupCohomologyCoefficientIso p (PrimeLocalRing.{u} p) A n hS sat)
  apply acyclic_of_iso (F.nativeCohomologyMackeyCentricIso n).symm
  exact F.saturated_fusion_sharpness_primeLocal_unconditional p hS sat
    (F.nativeGroupCohomologyMackey n)

end Sharpness.FusionSystem.CentricLinkingSystem
