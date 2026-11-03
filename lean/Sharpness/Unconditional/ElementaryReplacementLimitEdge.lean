import Sharpness.Unconditional.ElementaryCochainEdgeComparison
import Sharpness.CochainReplacementHorizontal
import Sharpness.CoefficientZeroLimitIso
import Sharpness.ProductCochainHomologyProjection
import Sharpness.ReplacementAugmentationProjection
import Sharpness.Unconditional.CategoryBarCalculation

/-! The elementary replacement edge to the actual inverse limit, with every
object component fixed by the actual total projection. Positive higher-limit
vanishing makes this same map an isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits HomologicalComplex Simplicial Opposite
open ElementaryCochainEdge
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def replacementCohomologyDiagram (n : ℕ) : Cᵒᵖ ⥤ ModuleCat.{u} R :=
  D ⋙ homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

theorem replacementHorizontal_zero_projection (n : ℕ) (P : C) :
    (cochainReplacementHorizontalIso D n).hom.f 0 ≫
      coefficientZeroEvaluation (replacementCohomologyDiagram D n) P =
      homologyMap (productCochainsProjection
        (fun s : ComposableArrows C 0 => D.obj (op (chainHead s)))
          (ComposableArrows.mk₀ P)) n := by
  change (𝟙 _ ≫ (productCochainsHomologyIso
      (fun s : ComposableArrows C 0 => D.obj (op (chainHead s))) n).hom) ≫
        ModuleCat.ofHom (LinearMap.proj (ComposableArrows.mk₀ P)) = _
  rw [Category.id_comp]
  exact productCochainsHomologyIso_projection _ n _

@[reassoc] theorem replacementHorizontal_cycles_component (n : ℕ) :
    cyclesMap (cochainReplacementHorizontalIso D n).hom 0 ≫
      (coefficientCochains (replacementCohomologyDiagram D n)).iCycles 0 =
      (verticalHomology (cochainReplacementBicomplex D) n).iCycles 0 ≫
        (cochainReplacementHorizontalIso D n).hom.f 0 :=
  cyclesMap_i (cochainReplacementHorizontalIso D n).hom 0

/-- Actual zero-column edge, independently of any acyclicity hypothesis. -/
def elementaryReplacementLimitEdge (n : ℕ) :
    (cochainReplacementTotal D).homology n ⟶ limit (replacementCohomologyDiagram D n) :=
  edgeMap (cochainReplacementBicomplex D) n ≫
    (edgeKernelCyclesIso (cochainReplacementBicomplex D) n).hom ≫
      cyclesMap (cochainReplacementHorizontalIso D n).hom 0 ≫
        coefficientZeroCyclesToLimit (replacementCohomologyDiagram D n)

/-- Every component is the native homology map of the actual replacement
projection to that object. -/
@[reassoc] theorem elementaryReplacementLimitEdge_component (n : ℕ) (P : C) :
    elementaryReplacementLimitEdge D n ≫ limit.π (replacementCohomologyDiagram D n) (op P) =
      homologyMap (replacementTotalProjection D (ComposableArrows.mk₀ P)) n := by
  simp only [elementaryReplacementLimitEdge, Category.assoc,
    coefficientZeroCyclesToLimit_projection, replacementHorizontal_cycles_component_assoc,
    edgeKernelCyclesIso_iCycles_assoc, edgeMap_kernelSubtype_assoc]
  rw [replacementHorizontal_zero_projection, ← homologyMap_comp]
  rfl

/-- Actual bar cohomology and the native horizontal comparison supply precisely
the positive-horizontal-exactness premise of the elementary edge theorem. -/
theorem replacement_positiveHorizontalExact
    (h : ∀ q p : ℕ, IsZero (higherLimit (replacementCohomologyDiagram D q) (p+1))) :
    PositiveHorizontalExact (cochainReplacementBicomplex D) := by
  intro q p
  have hc : (coefficientCochains (replacementCohomologyDiagram D q)).ExactAt (p+1) := by
    apply (exactAt_iff_isZero_homology _ _).mpr
    exact (h q p).of_iso ((Unconditional.categoryBarCohomologyNatIso (R := R) (C := C)
      (p+1)).app (replacementCohomologyDiagram D q)).symm
  exact hc.of_iso (cochainReplacementHorizontalIso D q).symm

theorem elementaryReplacementLimitEdge_isIso
    (h : ∀ q p : ℕ, IsZero (higherLimit (replacementCohomologyDiagram D q) (p+1)))
    (n : ℕ) : IsIso (elementaryReplacementLimitEdge D n) := by
  letI := edgeMap_isIso (cochainReplacementBicomplex D) (replacement_positiveHorizontalExact D h) n
  haveI : IsIso (cyclesMap (cochainReplacementHorizontalIso D n).hom 0) :=
    (cyclesFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) 0).map_isIso _
  haveI : IsIso (coefficientZeroCyclesToLimit (replacementCohomologyDiagram D n)) :=
    inferInstanceAs (IsIso (coefficientZeroCyclesLimitIso (replacementCohomologyDiagram D n)).hom)
  unfold elementaryReplacementLimitEdge
  infer_instance

def elementaryReplacementLimitIso
    (h : ∀ q p : ℕ, IsZero (higherLimit (replacementCohomologyDiagram D q) (p+1)))
    (n : ℕ) : (cochainReplacementTotal D).homology n ≅
      limit (replacementCohomologyDiagram D n) := by
  letI := elementaryReplacementLimitEdge_isIso D h n
  exact asIso (elementaryReplacementLimitEdge D n)

@[simp] theorem elementaryReplacementLimitIso_hom
    (h : ∀ q p : ℕ, IsZero (higherLimit (replacementCohomologyDiagram D q) (p+1))) (n : ℕ) :
    (elementaryReplacementLimitIso D h n).hom = elementaryReplacementLimitEdge D n := rfl

@[reassoc] theorem elementaryReplacementLimitIso_component
    (h : ∀ q p : ℕ, IsZero (higherLimit (replacementCohomologyDiagram D q) (p+1)))
    (n : ℕ) (P : C) :
    (elementaryReplacementLimitIso D h n).hom ≫ limit.π (replacementCohomologyDiagram D n) (op P) =
      homologyMap (replacementTotalProjection D (ComposableArrows.mk₀ P)) n :=
  elementaryReplacementLimitEdge_component D n P

end Sharpness
