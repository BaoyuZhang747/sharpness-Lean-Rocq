import Sharpness.CochainReplacementSecondPage
import Sharpness.ColumnConvergenceFiltration
import Sharpness.SpectralEdgePages
import Sharpness.SingularCochainFunctor
import Sharpness.Unconditional.CategoryBarCalculation

/-! The cohomological Bousfield--Kan model obtained by filtering the actual
singular-cochain replacement of a space diagram by its category degree.
The native pages, differentials, E2 computation and finite total convergence
are constructed; a vanishing hypothesis only enters the collapse theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.BousfieldKanReplacement
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] (R : Type u) [CommRing R]
    (A : ModuleCat.{u} R) (D : C ⥤ TopCat.{u})

def cochainDiagram : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  D.op ⋙ SingularCohomology.cochainFunctor R A

def cohomologyDiagram (n : ℕ) : CoefficientCategory R C :=
  cochainDiagram R A D ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{u} R) (ComplexShape.up ℕ) n

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  cochainReplacementBicomplex (cochainDiagram R A D)

def totalCochains : CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainReplacementTotal (cochainDiagram R A D)

def sequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R) :=
  totalColumnE₂SpectralSequence (bicomplex R A D)

def secondPageHigherLimitIso (i n : ℕ) :
    ((sequence R A D).page 2).X (i,n) ≅ higherLimit (cohomologyDiagram R A D n) i :=
  cochainReplacementSecondPageHigherLimitIso
    (Unconditional.categoryBarCalculationInput (R := R) (C := C)) (cochainDiagram R A D) i n

def totalConvergence : FiniteSpectralConvergence (sequence R A D)
    (fun n => (totalCochains R A D).homology n) :=
  totalColumnConvergence (bicomplex R A D)

theorem secondPage_isZero (h : ∀ n, Acyclic (cohomologyDiagram R A D n))
    (i n : ℕ) (hi : 0 < i) : IsZero (((sequence R A D).page 2).X (i,n)) :=
  IsZero.of_iso (h n i hi) (secondPageHigherLimitIso R A D i n)

theorem positive_columns_isZero (h : ∀ n, Acyclic (cohomologyDiagram R A D n))
    (r i n : ℕ) (hi : 0 < i) :
    IsZero (((sequence R A D).page (r+2) (by omega)).X (i,n)) :=
  spectralSequence_positive_columns_zero (sequence R A D)
    (fun pq hp => secondPage_isZero R A D h pq.1 pq.2 hp) r (i,n) hi

theorem differential_eq_zero (h : ∀ n, Acyclic (cohomologyDiagram R A D n))
    (r : ℕ) (pq ab : ℕ × ℕ) :
    ((sequence R A D).page (r+2) (by omega)).d pq ab = 0 :=
  spectralSequence_d_zero_of_column_zero (sequence R A D)
    (fun pq hp => secondPage_isZero R A D h pq.1 pq.2 hp) r pq ab

theorem zeroColumnBack_isIso (h : ∀ n, Acyclic (cohomologyDiagram R A D n))
    (r n : ℕ) : IsIso (spectralZeroColumnBack (sequence R A D) r n) :=
  spectralZeroColumnBack_isIso (sequence R A D)
    (fun pq hp => secondPage_isZero R A D h pq.1 pq.2 hp) r n

theorem collapses_onto_vertical_axis (h : ∀ n, Acyclic (cohomologyDiagram R A D n)) :
    (∀ r i n : ℕ, 0 < i → IsZero (((sequence R A D).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ), ((sequence R A D).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack (sequence R A D) r n)) :=
  ⟨positive_columns_isZero R A D h, differential_eq_zero R A D h, zeroColumnBack_isIso R A D h⟩

end Sharpness.BousfieldKanReplacement
