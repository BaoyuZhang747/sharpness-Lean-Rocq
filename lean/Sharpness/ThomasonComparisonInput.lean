import Sharpness.GrothendieckDiagonalString
import Sharpness.CategorySimplicialReplacement
import Sharpness.SimplicialReplacementLinearization
import Mathlib.Algebra.Homology.QuasiIso

/-! Uniform standard Thomason comparison, in the covariant head
convention of Mandell, An Inverse K-Theory Functor, Lemma 5.1,
printed p.781 (restating Thomason 1979, Theorem 1.2).
The supplied simplex formula is the native well-typed string functor,
not the following display's unresolved prefix-index notation.
The R-chain consequence uses the usual simplicial/realization
homology comparison (Weibel 8.2.3-8.2.4) and change of coefficients
(Weibel 3.6.1). This is an explicitly recorded standard consequence,
not a claim that Mandell displays an R-module chain complex.
The record quantifies over every category-valued diagram and every
map with the canonical simplex formula. No comma construction,
linking system, augmentation, spectral sequence or module A occurs.
See sources/GeometricComparisonReferences.provenance.json. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

structure ThomasonComparisonInput (R : Type u) [CommRing R] where
  Thomason_Mandell_5_1 : ∀ {C : Type u} [Category.{u} C] (B : C ⥤ Cat.{u,u})
    (t : simplicialReplacementDiagonal (B ⋙ CategoryTheory.nerveFunctor) ⟶
      CategoryTheory.nerve (Grothendieck B)),
    (∀ (i : SimplexCategoryᵒᵖ) (s : ComposableArrows C i.unop.len)
      (x : ComposableArrows (B.obj (chainHead s)) i.unop.len),
      t.app i ⟨s, x⟩ = grothendieckDiagonalString B s x) →
    QuasiIso ((simplicialChainsFunctor R).map t)

end Sharpness
