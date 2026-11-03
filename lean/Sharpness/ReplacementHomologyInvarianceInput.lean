import Sharpness.SimplicialReplacementFunctor
import Sharpness.SimplicialReplacementLinearization
import Mathlib.Algebra.Homology.QuasiIso

/-! Standard homology-invariance consequence for the ordinary
unnormalized simplicial replacement. The reference statement is
uniform in arbitrary diagrams and coefficient rings, not an
augmentation theorem. It follows by taking the direct sums of the
objectwise free chain maps, using the first-quadrant column spectral
sequence (Weibel 5.6.1), its comparison theorem 5.2.12, and the natural
Eilenberg-Zilber comparison 8.5.1/8.5.4. Both totalization signs here
are the standard d_h + (-1)^p d_v convention.
This uniform standard consequence is explicitly separated from the
literal source statements in the provenance file. It does not assert
the manuscript's E2, convergence, restriction edge or augmentation.
See sources/GeometricComparisonReferences.provenance.json. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

structure ReplacementHomologyInvarianceInput (R : Type u) [CommRing R] where
  Weibel_5_2_12_5_6_1_8_5_1 : ∀ {C : Type u} [Category.{u} C]
    {D E : C ⥤ SSet.{u}} (a : D ⟶ E),
    (∀ P, QuasiIso ((simplicialChainsFunctor R).map (a.app P))) →
    QuasiIso ((simplicialChainsFunctor R).map (simplicialReplacementDiagonalMap a))

end Sharpness
