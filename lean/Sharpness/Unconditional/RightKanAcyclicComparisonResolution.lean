import Sharpness.Unconditional.InjectiveHigherLimits
import Sharpness.Unconditional.DerivedDetection
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! A left exact functor sends an injective resolution to a resolution whenever
the mapped complex is exact in positive degrees. Degree zero is supplied by
preservation of the actual augmentation kernel, not by a vanishing assumption.
The adjunction then compares the original module-valued Ext groups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type v} [Category.{u} C] [Abelian C]
    {D : Type w} [Category.{u} D] [Abelian D]

/-- Map an actual injective resolution through a left exact functor preserving
injectives, assuming only positive-degree acyclicity of the mapped complex. -/
def mapInjectiveResolutionOfPositiveExactness
    (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    [G.PreservesInjectiveObjects] {Y : D} (I : InjectiveResolution Y)
    (hI : ∀ n : ℕ, ((G.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1)) :
    InjectiveResolution (G.obj Y) where
  cocomplex := (G.mapHomologicalComplex _).obj I.cocomplex
  injective n := G.injective_obj (I.cocomplex.X n)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨G.map (I.ι.f 0), by
      change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
      rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · dsimp only [HomologicalComplex.shortComplexFunctor']
        constructor
        · simpa only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using!
            (ShortComplex.exact_of_f_is_kernel
              ((ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).map G)
              (KernelFork.mapIsLimit _ I.isLimitKernelFork G))
        · simpa only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero] using!
            (inferInstance : Mono (G.map (I.ι.f 0)))
      · rfl
      · rfl
      · change G.map (I.cocomplex.d 0 0) = 0
        simp
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · exact hI n
      · apply CochainComplex.exactAt_succ_single_obj⟩

variable (R : Type u) [CommRing R] [Linear R C] [Linear R D]
    [EnoughProjectives C] [EnoughInjectives C]
    [EnoughProjectives D] [EnoughInjectives D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [G.Additive] [G.Linear R]
    [L.PreservesMonomorphisms]

/-- The actual Ext comparison through a right adjoint with no positive derived
value at the coefficient object. No degree-zero vanishing is required. -/
def extRightAdjointIsoOfPositiveExactness
    (adj : L ⊣ G) (X : C) (Y : D) (I : InjectiveResolution Y)
    (hI : ∀ n : ℕ, ((G.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1))
    (n : ℕ) :
    ((Ext R D n).obj (op (L.obj X))).obj Y ≅
      ((Ext R C n).obj (op X)).obj (G.obj Y) := by
  letI := adj.isRightAdjoint
  letI : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let J := mapInjectiveResolutionOfPositiveExactness G I hI
  exact extInjectiveHomologyIso R (L.obj X) Y I n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
      (adjunctionLinearCoyonedaComplexIso R adj X I.cocomplex) ≪≫
    (extInjectiveHomologyIso R X (G.obj Y) J n).symm

end Sharpness
