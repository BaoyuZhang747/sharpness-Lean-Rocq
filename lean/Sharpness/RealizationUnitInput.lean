import Sharpness.RealizationDiagramUnit
import Sharpness.SimplicialReplacementLinearization
import Mathlib.Algebra.Homology.QuasiIso

/-! Uniform standard realization input, with its coefficient boundary
explicit: May, Simplicial Objects in Algebraic Topology, Proposition
16.2(i), printed p.63, states the integral homology isomorphism of the
actual adjunction unit. The free R-coefficient consequence is the
standard change-of-coefficients consequence of Weibel, Theorem 3.6.1,
printed p.87; Weibel 8.2.3-8.2.4 identify the chain models used here.
This record is uniform in every simplicial set. It has no category
diagram, Grothendieck comparison, augmentation, coefficient module A,
spectral sequence, or manuscript conclusion as a field.
See sources/RealizationUnitReferences.provenance.json. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

structure RealizationUnitInput (R : Type u) [CommRing R] where
  May_16_2_Weibel_3_6_1 : ∀ X : SSet.{u},
    QuasiIso ((simplicialChainsFunctor R).map (realizationSingularUnit X))

end Sharpness
