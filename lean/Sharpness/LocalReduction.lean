import Sharpness.ArbitraryCoefficients
import Sharpness.MackeyCoefficientFunctors
import Sharpness.ScalarSubquotients
import Sharpness.BarFiniteGeneration

/-! The three original reduction steps of cor:local, for a Noetherian
ring and a scalar in its Jacobson radical. The p-annihilated case will
be supplied by the proved field theorem, not by a bibliography field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]

def centricCoefficientMap
    {M N : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape} (f : M ⟶ N) :
    F.centricCoefficient M ⟶ F.centricCoefficient N :=
  Functor.whiskerLeft F.centricInclusion.op (F.coefficientFunctor.map f)

def centricCoefficientIso
    {M N : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape} (e : M ≅ N) :
    F.centricCoefficient M ≅ F.centricCoefficient N :=
  Functor.isoWhiskerLeft F.centricInclusion.op (F.coefficientFunctor.mapIso e)

variable (bar : FiniteBarModel R F.CentricOrbit) (r : R)
    (killedExact : ∀ (A : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape),
      (∀ P (x : A.Value P), r • x = 0) → bar.ExactPositive (F.centricCoefficient A))

include killedExact

theorem scalar_surjective_mackey_cohomology
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (n : ℕ) :
    Function.Surjective (fun x : bar.Cohomology (F.centricCoefficient M) n => r • x) := by
  apply bar.scalar_surjective_on_cohomology
    (F.centricCoefficientMap (M.submoduleInclusion (M.scalarKernel r)))
    (F.centricCoefficientMap (M.scalarToImage r))
    (F.centricCoefficientMap (M.submoduleInclusion (M.scalarImage r)))
    (F.centricCoefficientMap (M.quotientProjection (M.scalarImage r)))
  · intro P; exact Subtype.val_injective
  · intro P; exact M.scalarToImage_surjective r P.unop.obj
  · intro P; exact M.scalarKernel_exact r P.unop.obj
  · intro P; exact Subtype.val_injective
  · intro P; exact (M.scalarImage r).obj P.unop.obj |>.mkQ_surjective
  · intro P; exact M.scalarImage_exact r P.unop.obj
  · exact killedExact _ (M.scalarKernel_killed r)
  · exact killedExact _ (M.scalarQuotient_killed r)
  · intro P x; rfl

/-- The divisibility conclusion on the actual native Ext object, using
the R-linear general bar identification. -/
theorem scalar_surjective_mackey_higherLimit
    [EnoughProjectives (CoefficientCategory R F.CentricOrbit)]
    (cmp : bar.Comparison)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (i : ℕ) (hi : 0 < i) :
    Function.Surjective (fun x : higherLimit (F.centricCoefficient M) i => r • x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  let e := (cmp.AKO_III_5_3 (F.centricCoefficient M) n).toLinearEquiv
  intro x
  obtain ⟨y, hy⟩ := F.scalar_surjective_mackey_cohomology bar r killedExact M n (e x)
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  rw [map_smul, e.apply_symm_apply]
  exact hy

theorem finite_local_exact_of_killed_exact [IsNoetherianRing R]
    (hr : r ∈ Ideal.jacobson (⊥ : Ideal R))
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)
    [∀ P, Module.Finite R (M.Value P)] : bar.ExactPositive (F.centricCoefficient M) := by
  haveI (P : F.CentricOrbitᵒᵖ) : Module.Finite R ((F.centricCoefficient M).obj P) :=
    inferInstanceAs (Module.Finite R (M.Value P.unop.obj))
  exact bar.exactPositive_of_fg_of_scalar_surjective _ r hr
    (F.scalar_surjective_mackey_cohomology bar r killedExact M)

theorem arbitrary_local_exact_of_killed_exact [IsNoetherianRing R]
    (hr : r ∈ Ideal.jacobson (⊥ : Ideal R))
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    bar.ExactPositive (F.centricCoefficient M) := by
  apply F.exactPositive_of_finite_subfunctors M bar
  intro X
  haveI (P : F.Orbit) : Module.Finite R
      ((M.submodule (M.finiteGeneratedSubfunctor X)).Value P) :=
    Module.Finite.of_fg (M.finiteGeneratedValue_fg X P)
  exact F.finite_local_exact_of_killed_exact bar r killedExact hr _

end Sharpness.FusionSystem
