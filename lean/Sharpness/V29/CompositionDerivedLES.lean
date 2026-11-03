import Sharpness.V29.CompositionDerived

/-! All three exact positions of the literal derived-limit long exact
sequence, and its initial degree-zero monomorphism. The cochain sequence
is transported through the proved natural category-bar comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits

private theorem exact_of_comparison {R : Type u} [CommRing R]
    {A B C A' B' C' : ModuleCat.{u} R}
    (a : A ≅ A') (b : B ≅ B') (c : C ≅ C')
    (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')
    (hf : ∀ x, b.hom (f x) = f' (a.hom x))
    (hg : ∀ x, c.hom (g x) = g' (b.hom x))
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro x
  constructor
  · intro hx
    have hx' : g' (b.hom x) = 0 := by rw [← hg, hx, map_zero]
    obtain ⟨y, hy⟩ := (h (b.hom x)).mp hx'
    refine ⟨a.inv y, ?_⟩
    apply b.toLinearEquiv.injective
    change b.hom (f (a.inv y)) = b.hom x
    have ha : a.hom (a.inv y) = y := a.toLinearEquiv.apply_symm_apply y
    rw [hf, ha, hy]
  · rintro ⟨y, rfl⟩
    apply c.toLinearEquiv.injective
    change c.hom (g (f y)) = c.hom 0
    rw [hg, hf, h.apply_apply_eq_zero, map_zero]

variable {S R : Type u} [Group S] [Finite S] [CommRing R]
    (F : FusionSystem S)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (N : M.Subfunctor)

/-- The native higher-limit map induced by the actual subfunctor inclusion. -/
def compositionDerivedInclusion (n : ℕ) :=
  (higherLimitFunctor R F.CentricOrbit n).map (F.subCoefficientInclusion M N)

/-- The native higher-limit map induced by the actual quotient projection. -/
def compositionDerivedProjection (n : ℕ) :=
  (higherLimitFunctor R F.CentricOrbit n).map (F.quotientCoefficientProjection M N)

theorem compositionDerivedInclusion_comparison (n : ℕ) :
    compositionDerivedInclusion F M N n ≫
        (Unconditional.categoryBarCohomologyIso (F.centricCoefficient M) n).hom =
      (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.submodule N)) n).hom ≫
        HomologicalComplex.homologyMap
          ((compositionCoefficientSequence F M N).map coefficientCochainFunctor).f n :=
  (Unconditional.categoryBarCohomologyNatIso n).hom.naturality _

theorem compositionDerivedProjection_comparison (n : ℕ) :
    compositionDerivedProjection F M N n ≫
        (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.quotient N)) n).hom =
      (Unconditional.categoryBarCohomologyIso (F.centricCoefficient M) n).hom ≫
        HomologicalComplex.homologyMap
          ((compositionCoefficientSequence F M N).map coefficientCochainFunctor).g n :=
  (Unconditional.categoryBarCohomologyNatIso n).hom.naturality _

/-- Exactness at the native higher limit of M/N. -/
theorem compositionDerived_exact_projection_connecting (n : ℕ) :
    Function.Exact (compositionDerivedProjection F M N n)
      (compositionDerivedConnecting F M N n) := by
  apply exact_of_comparison
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient M) n)
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.quotient N)) n)
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.submodule N)) (n + 1))
    _ _ (HomologicalComplex.homologyMap
      ((compositionCoefficientSequence F M N).map coefficientCochainFunctor).g n)
      (compositionConnecting F M N n)
  · intro x
    convert congrArg (fun f => f x) (compositionDerivedProjection_comparison F M N n) using 1 <;> rfl
  · intro x
    simpa only [ModuleCat.comp_apply] using
      congrArg (fun f => f x) (compositionDerivedConnecting_comparison F M N n)
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((compositionCochainSequence_shortExact F M N).homology_exact₃ n (n + 1) (by simp))

/-- Exactness at the native higher limit of N in the following degree. -/
theorem compositionDerived_exact_connecting_inclusion (n : ℕ) :
    Function.Exact (compositionDerivedConnecting F M N n)
      (compositionDerivedInclusion F M N (n + 1)) := by
  apply exact_of_comparison
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.quotient N)) n)
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient (M.submodule N)) (n + 1))
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient M) (n + 1))
    _ _ (compositionConnecting F M N n)
      (HomologicalComplex.homologyMap
        ((compositionCoefficientSequence F M N).map coefficientCochainFunctor).f (n + 1))
  · intro x
    simpa only [ModuleCat.comp_apply] using
      congrArg (fun f => f x) (compositionDerivedConnecting_comparison F M N n)
  · intro x
    convert congrArg (fun f => f x) (compositionDerivedInclusion_comparison F M N (n + 1)) using 1 <;> rfl
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((compositionCochainSequence_shortExact F M N).homology_exact₁ n (n + 1) (by simp))

/-- The complete three-position native long exact sequence, in every degree. -/
theorem compositionDerived_longExact (n : ℕ) :
    Function.Exact (compositionDerivedInclusion F M N n) (compositionDerivedProjection F M N n) ∧
    Function.Exact (compositionDerivedProjection F M N n) (compositionDerivedConnecting F M N n) ∧
    Function.Exact (compositionDerivedConnecting F M N n) (compositionDerivedInclusion F M N (n + 1)) := by
  refine ⟨?_, compositionDerived_exact_projection_connecting F M N n,
    compositionDerived_exact_connecting_inclusion F M N n⟩
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (compositionDerived_exact F M N n)

/-- The initial native degree-zero inclusion is a monomorphism. -/
theorem compositionDerivedInclusion_zero_mono : Mono (compositionDerivedInclusion F M N 0) := by
  let U := (compositionCoefficientSequence F M N).map coefficientCochainFunctor
  have hU : U.ShortExact := compositionCochainSequence_shortExact F M N
  haveI : Mono U.f := hU.mono_f
  haveI : Mono (HomologicalComplex.homologyMap U.f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel U.f 0 (by intro i; simp)
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  apply (Unconditional.categoryBarCohomologyIso
    (F.centricCoefficient (M.submodule N)) 0).toLinearEquiv.injective
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap U.f 0)).mp inferInstance
  have hx := congrArg (fun f => f x) (compositionDerivedInclusion_comparison F M N 0)
  have hy := congrArg (fun f => f y) (compositionDerivedInclusion_comparison F M N 0)
  simp only [ModuleCat.comp_apply] at hx hy
  exact hx.symm.trans ((congrArg
    (Unconditional.categoryBarCohomologyIso (F.centricCoefficient M) 0).hom hxy).trans hy)

end Sharpness.FusionSystem.V29

#check Sharpness.FusionSystem.V29.compositionDerived_longExact
#check Sharpness.FusionSystem.V29.compositionDerivedInclusion_zero_mono
#print axioms Sharpness.FusionSystem.V29.compositionDerived_longExact
#print axioms Sharpness.FusionSystem.V29.compositionDerivedInclusion_zero_mono
