import Sharpness.V29.CompositionSeries
import Sharpness.ArbitraryCoefficients
import Sharpness.Unconditional.ScalarImageHigherIso
import Sharpness.Unconditional.BarCalculation
import Sharpness.FullSubcategoryFinite
import Sharpness.ZeroCoefficients

/-! The actual short exact sequences and higher-limit homology sequences
for the factors of a finite full-Mackey composition series. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits
open MackeyModule.V29

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]

/-- The coefficient sequence uses the literal subtype inclusion and quotient
projection at every centric subgroup. -/
def compositionCoefficientSequence
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor) :
    ShortComplex (CoefficientCategory R F.CentricOrbit) :=
  ShortComplex.mk (F.subCoefficientInclusion M N) (F.quotientCoefficientProjection M N)
    (by
      ext P x
      exact (LinearMap.exact_subtype_mkQ (N.obj P.unop.obj)).apply_apply_eq_zero x)

theorem compositionCoefficientSequence_pointwise_injective
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)
    (P : F.CentricOrbitᵒᵖ) :
    Function.Injective ((compositionCoefficientSequence F M N).f.app P) :=
  Subtype.val_injective

theorem compositionCoefficientSequence_pointwise_surjective
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)
    (P : F.CentricOrbitᵒᵖ) :
    Function.Surjective ((compositionCoefficientSequence F M N).g.app P) :=
  (N.obj P.unop.obj).mkQ_surjective

theorem compositionCoefficientSequence_pointwise_exact
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)
    (P : F.CentricOrbitᵒᵖ) :
    Function.Exact ((compositionCoefficientSequence F M N).f.app P)
      ((compositionCoefficientSequence F M N).g.app P) :=
  LinearMap.exact_subtype_mkQ (N.obj P.unop.obj)

/-- This is a short exact sequence of the actual coefficient cochain
complexes. Its homology sequence computes the derived limits by the proved
category-bar comparison. -/
theorem compositionCochainSequence_shortExact
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor) :
    ((compositionCoefficientSequence F M N).map coefficientCochainFunctor).ShortExact :=
  coefficientCochain_shortExact (compositionCoefficientSequence F M N)
    (compositionCoefficientSequence_pointwise_injective F M N)
    (compositionCoefficientSequence_pointwise_surjective F M N)
    (compositionCoefficientSequence_pointwise_exact F M N)

/-- The connecting maps of the actual long exact sequence, retained explicitly
for inspection. The natural category-bar isomorphism identifies its source
and target with the corresponding right derived inverse limits. -/
def compositionConnecting
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor) (n : ℕ) :=
  (compositionCochainSequence_shortExact F M N).δ n (n + 1) (by simp)

/-- Extension closure is proved through the long exact sequence of actual
coefficient complexes and the natural comparison with derived limits.
Neither the old cocycle extension proof nor the final sharpness theorem is used. -/
theorem composition_extension_acyclic
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)
    (hN : Acyclic (F.centricCoefficient (M.submodule N)))
    (hQ : Acyclic (F.centricCoefficient (M.quotient N))) :
    Acyclic (F.centricCoefficient M) := by
  intro n hn
  haveI : IsIso ((higherLimitFunctor R F.CentricOrbit n).map
      (F.quotientCoefficientProjection M N)) := higherLimit_map_isIso_of_kernel_acyclic
    (F.subCoefficientInclusion M N) (F.quotientCoefficientProjection M N)
    (fun _ => Subtype.val_injective)
    (fun P => (N.obj P.unop.obj).mkQ_surjective)
    (fun P => LinearMap.exact_subtype_mkQ (N.obj P.unop.obj)) hN n hn
  exact IsZero.of_iso (hQ n hn)
    (asIso ((higherLimitFunctor R F.CentricOrbit n).map
      (F.quotientCoefficientProjection M N)))

variable {k : Type u} [Field k]

/-- A finite composition series for this particular M suffices: the premise
mentions only its actual simple factors, not every simple Mackey functor. -/
theorem acyclic_of_compositionSeries
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (series : CompositionSeries M)
    (factors : ∀ A ∈ series.factors, Acyclic (F.centricCoefficient A)) :
    Acyclic (F.centricCoefficient M) := by
  induction series with
  | nil M hz =>
    apply (Unconditional.finiteCategoryBarModel k F.CentricOrbit).acyclic_of_values_zero
      (F.centricCoefficient M) (Unconditional.finiteCategoryBarComparison k F.CentricOrbit)
    intro P x
    exact hz P.unop.obj x
  | cons M N hs tail ih =>
    apply composition_extension_acyclic F M N
    · exact factors (M.submodule N) (by simp [CompositionSeries.factors])
    · apply ih
      intro A hA
      exact factors A (by simp [CompositionSeries.factors, hA])

end Sharpness.FusionSystem.V29
