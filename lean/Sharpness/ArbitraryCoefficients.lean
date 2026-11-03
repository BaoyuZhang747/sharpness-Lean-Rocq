import Sharpness.BarExactness
import Sharpness.MackeySubquotients
import Sharpness.NormalForms

/-!
Manuscript Lemma 2.4 on the concrete fusion orbit category. Finite length
is connected to actual derived limits, and the arbitrary-value step is
proved by lifting a finite bar cocycle into a finitely generated Mackey
subfunctor. Continuity or simple-to-all sharpness is not assumed.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)

def subCoefficientInclusion (N : M.Subfunctor) :
    F.centricCoefficient (M.submodule N) ⟶ F.centricCoefficient M where
  app P := ModuleCat.ofHom (N.obj P.unop.obj).subtype
  naturality _ _ _ := by apply ModuleCat.hom_ext; rfl

def quotientCoefficientProjection (N : M.Subfunctor) :
    F.centricCoefficient M ⟶ F.centricCoefficient (M.quotient N) where
  app P := ModuleCat.ofHom (N.obj P.unop.obj).mkQ
  naturality _ _ _ := by apply ModuleCat.hom_ext; rfl

variable (bar : FiniteBarModel R F.CentricOrbit)

theorem exactPositive_zero (zero : ∀ P, ∀ x : M.Value P, x = 0) :
    bar.ExactPositive (F.centricCoefficient M) := by
  intro n z _
  refine ⟨0, ?_⟩
  rw [map_zero]
  funext i
  exact (zero _ (z i)).symm

theorem exactPositive_extension (N : M.Subfunctor)
    (hN : bar.ExactPositive (F.centricCoefficient (M.submodule N)))
    (hQ : bar.ExactPositive (F.centricCoefficient (M.quotient N))) :
    bar.ExactPositive (F.centricCoefficient M) := by
  apply bar.exactPositive_extension
    (F.subCoefficientInclusion M N) (F.quotientCoefficientProjection M N)
  · intro P; exact Subtype.val_injective
  · intro P; exact (N.obj P.unop.obj).mkQ_surjective
  · intro P; exact LinearMap.exact_subtype_mkQ (N.obj P.unop.obj)
  · exact hN
  · exact hQ

variable {k : Type u} [Field k]
    (barK : FiniteBarModel k F.CentricOrbit)

/-- Finite-valued simple reduction, using the actual full Mackey quotient
and a proved cocycle extension argument. -/
theorem finite_acyclic_of_simple
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    (cmp : barK.Comparison)
    (simple : ∀ A : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape,
      A.IsSimple → Acyclic (F.centricCoefficient A))
    (A : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    [∀ P, FiniteDimensional k (A.Value P)] : Acyclic (F.centricCoefficient A) := by
  classical
  letI : Fintype F.Orbit := Fintype.ofFinite _
  apply (barK.acyclic_iff cmp _).mpr
  apply MackeyModule.finite_dimensional_reduction
    (fun A => barK.ExactPositive (F.centricCoefficient A))
  · intro A _ hzero
    exact F.exactPositive_zero A barK hzero
  · intro A _ hs
    exact (barK.acyclic_iff cmp _).mp (simple A hs)
  · intro A _ N hN hQ
    exact F.exactPositive_extension A barK N hN hQ

/-- Every cocycle of arbitrary coefficients lies in one finitely generated
full Mackey subfunctor: the finite set contains its subgroup-tagged entries.
The equation d z = 0 descends because the inclusions are injective. -/
theorem exactPositive_of_finite_subfunctors
    (finiteValues : ∀ (X : Finset (Σ P : F.Orbit, M.Value P)),
      bar.ExactPositive (F.centricCoefficient (M.submodule (M.finiteGeneratedSubfunctor X)))) :
    bar.ExactPositive (F.centricCoefficient M) := by
  classical
  intro n z hz
  let label : bar.Index (n+1) → Σ P : F.Orbit, M.Value P :=
    fun i => ⟨(bar.source (n+1) i).unop.obj, z i⟩
  let X : Finset (Σ P : F.Orbit, M.Value P) := Finset.univ.image label
  let N := M.finiteGeneratedSubfunctor X
  have memN (i : bar.Index (n+1)) : z i ∈ N.obj (bar.source (n+1) i).unop.obj := by
    apply Submodule.subset_span
    refine ⟨label i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      ⟨(bar.source (n+1) i).unop.obj, 𝟙 _, 𝟙 _⟩, ?_⟩
    simp [MackeyModule.normalMap, M.pull_id, M.push_id, label]
  let zN : bar.Cochains (F.centricCoefficient (M.submodule N)) (n+1) :=
    fun i => ⟨z i, memN i⟩
  let inc := F.subCoefficientInclusion M N
  have lifted : bar.map inc (n+1) zN = z := rfl
  have closed : bar.d (F.centricCoefficient (M.submodule N)) (n+1) zN = 0 := by
    apply bar.map_injective inc (fun _ => Subtype.val_injective) (n+2)
    rw [map_zero, bar.map_d, lifted, hz]
  obtain ⟨b, hb⟩ := finiteValues X n zN closed
  refine ⟨bar.map inc n b, ?_⟩
  rw [← bar.map_d, hb, lifted]

/-- Manuscript Lemma 2.4: simple acyclicity implies acyclicity for every
full Mackey functor, including arbitrary-dimensional values. The sole
cohomology comparison is the finite bar computation of derived inverse limits,
constructed in `Unconditional.BarCalculation`. -/
theorem arbitrary_acyclic_of_simple
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    (cmp : barK.Comparison)
    (simple : ∀ A : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape,
      A.IsSimple → Acyclic (F.centricCoefficient A)) : F.Sharp (R := k) := by
  intro A
  apply (barK.acyclic_iff cmp _).mpr
  apply F.exactPositive_of_finite_subfunctors A barK
  intro X
  let N := A.finiteGeneratedSubfunctor X
  haveI (P : F.Orbit) : FiniteDimensional k ((A.submodule N).Value P) :=
    (Submodule.fg_iff_finiteDimensional _).mp (A.finiteGeneratedValue_fg X P)
  exact (barK.acyclic_iff cmp _).mp (F.finite_acyclic_of_simple barK cmp simple (A.submodule N))

end Sharpness.FusionSystem
