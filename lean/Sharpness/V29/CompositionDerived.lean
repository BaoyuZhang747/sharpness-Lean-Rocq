import Sharpness.V29.CompositionExact

/-! Literal derived-limit maps for each step of the composition series.
The connecting map is conjugated along the proved natural bar comparison;
this file does not assume a long exact sequence as extra input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits

variable {S R : Type u} [Group S] [Finite S] [CommRing R]
    (F : FusionSystem S)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)

local instance (n : ℕ) :
    (coefficientCohomologyFunctor (R := R) (C := F.CentricOrbit) n).PreservesZeroMorphisms := by
  unfold coefficientCohomologyFunctor
  infer_instance

local instance (n : ℕ) :
    (higherLimitFunctor R F.CentricOrbit n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (Unconditional.categoryBarCohomologyNatIso n).symm

/-- The actual derived-limit connecting map for `0 → N → M → M/N → 0`. -/
def compositionDerivedConnecting (n : ℕ) :
    higherLimit (F.centricCoefficient (M.quotient N)) n ⟶
      higherLimit (F.centricCoefficient (M.submodule N)) (n + 1) :=
  (Unconditional.categoryBarCohomologyIso
    (F.centricCoefficient (M.quotient N)) n).hom ≫
    compositionConnecting F M N n ≫
    (Unconditional.categoryBarCohomologyIso
      (F.centricCoefficient (M.submodule N)) (n + 1)).inv

/-- The connecting-map square commutes with the natural identification of
actual derived limits with coefficient cochain cohomology. -/
theorem compositionDerivedConnecting_comparison (n : ℕ) :
    compositionDerivedConnecting F M N n ≫
        (Unconditional.categoryBarCohomologyIso
          (F.centricCoefficient (M.submodule N)) (n + 1)).hom =
      (Unconditional.categoryBarCohomologyIso
        (F.centricCoefficient (M.quotient N)) n).hom ≫
        compositionConnecting F M N n := by
  simp [compositionDerivedConnecting]

/-- Exactness at the actual higher limit of M, with the maps induced by
the literal inclusion and projection. -/
theorem compositionDerived_exact (n : ℕ) :
    ((compositionCoefficientSequence F M N).map
      (higherLimitFunctor R F.CentricOrbit n)).Exact := by
  let T := compositionCoefficientSequence F M N
  have h : (T.map (coefficientCohomologyFunctor n)).Exact :=
    (compositionCochainSequence_shortExact F M N).homology_exact₂ n
  exact ShortComplex.exact_of_iso
    (T.mapNatIso (Unconditional.categoryBarCohomologyNatIso n)).symm h

end Sharpness.FusionSystem.V29
