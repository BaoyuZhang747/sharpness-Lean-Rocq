import Sharpness.LocalReduction
import Sharpness.Unconditional.CategoryBarCalculation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
The actual map from a coefficient module to the image of scalar
multiplication induces an isomorphism on positive higher limits when
the scalar kernel is acyclic. The proof uses the actual short exact
sequence of coefficient cochain complexes and its homology sequence.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Products of a pointwise short exact sequence form the actual short
exact sequence of coefficient cochain complexes. No finiteness is needed. -/
theorem coefficientCochain_shortExact
    (T : ShortComplex (CoefficientCategory R C))
    (hf : ∀ P, Function.Injective (T.f.app P))
    (hg : ∀ P, Function.Surjective (T.g.app P))
    (hex : ∀ P, Function.Exact (T.f.app P) (T.g.app P)) :
    (T.map coefficientCochainFunctor).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (fun s : ComposableArrows C n => T.g.app (op (chainHead s)) (x s)) = 0 at hx
    choose y hy using fun s : ComposableArrows C n =>
      (hex (op (chainHead s)) (x s)).mp (congrFun hx s)
    exact ⟨y, funext hy⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    funext s
    exact hf (op (chainHead s)) (congrFun hxy s)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    choose x hx using fun s : ComposableArrows C n => hg (op (chainHead s)) (y s)
    exact ⟨x, funext hx⟩

/-- For a pointwise short exact coefficient sequence, positive acyclicity
of the kernel makes the actual induced higher-limit map an isomorphism.
No degree-zero vanishing is assumed. -/
theorem higherLimit_map_isIso_of_kernel_acyclic
    {K D E : CoefficientCategory R C} (f : K ⟶ D) (g : D ⟶ E)
    (hf : ∀ P, Function.Injective (f.app P))
    (hg : ∀ P, Function.Surjective (g.app P))
    (hex : ∀ P, Function.Exact (f.app P) (g.app P))
    (hK : Acyclic K) (n : ℕ) (hn : 0 < n) :
    IsIso ((higherLimitFunctor R C n).map g) := by
  let T : ShortComplex (CoefficientCategory R C) := ShortComplex.mk f g (by
    ext P x
    exact (hex P).apply_apply_eq_zero x)
  let U := T.map coefficientCochainFunctor
  have hU : U.ShortExact := coefficientCochain_shortExact T hf hg hex
  have hzero (i : ℕ) (hi : 0 < i) : IsZero (U.X₁.homology i) :=
    IsZero.of_iso (hK i hi) (Unconditional.categoryBarCohomologyIso K i).symm
  haveI : Mono (HomologicalComplex.homologyMap U.g n) :=
    (hU.homology_exact₂ n).mono_g ((hzero n hn).eq_of_src _ _)
  haveI : Epi (HomologicalComplex.homologyMap U.g n) :=
    (hU.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((hzero (n + 1) (Nat.zero_lt_succ n)).eq_of_tgt _ _)
  have hmap : IsIso (HomologicalComplex.homologyMap U.g n) :=
    isIso_of_mono_of_epi _
  exact (NatIso.isIso_map_iff (Unconditional.categoryBarCohomologyNatIso n) g).mpr hmap

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (r : R)

/-- The actual coefficient map induced by `M → rM` is an isomorphism on
every positive higher limit whenever `M[r]` has vanishing positive higher
limits. This is the isomorphism asserted in the prime-local reduction. -/
theorem scalarToImage_higherLimit_isIso
    (hkernel : Acyclic (F.centricCoefficient (M.submodule (M.scalarKernel r))))
    (i : ℕ) (hi : 0 < i) :
    IsIso ((higherLimitFunctor R F.CentricOrbit i).map
      (F.centricCoefficientMap (M.scalarToImage r))) := by
  apply higherLimit_map_isIso_of_kernel_acyclic
    (F.centricCoefficientMap (M.submoduleInclusion (M.scalarKernel r)))
    (F.centricCoefficientMap (M.scalarToImage r))
  · intro P
    exact Subtype.val_injective
  · intro P
    exact M.scalarToImage_surjective r P.unop.obj
  · intro P
    exact M.scalarKernel_exact r P.unop.obj
  · exact hkernel
  · exact hi

/-- The induced isomorphism has the actual higher-limit map of scalar
multiplication onto its image as its forward morphism. -/
def scalarToImage_higherLimitIso
    (hkernel : Acyclic (F.centricCoefficient (M.submodule (M.scalarKernel r))))
    (i : ℕ) (hi : 0 < i) :
    higherLimit (F.centricCoefficient M) i ≅
      higherLimit (F.centricCoefficient (M.submodule (M.scalarImage r))) i := by
  letI : IsIso ((higherLimitFunctor R F.CentricOrbit i).map
      (F.centricCoefficientMap (M.scalarToImage r))) :=
    F.scalarToImage_higherLimit_isIso M r hkernel i hi
  exact asIso ((higherLimitFunctor R F.CentricOrbit i).map
    (F.centricCoefficientMap (M.scalarToImage r)))

@[simp] theorem scalarToImage_higherLimitIso_hom
    (hkernel : Acyclic (F.centricCoefficient (M.submodule (M.scalarKernel r))))
    (i : ℕ) (hi : 0 < i) :
    (F.scalarToImage_higherLimitIso M r hkernel i hi).hom =
      (higherLimitFunctor R F.CentricOrbit i).map
        (F.centricCoefficientMap (M.scalarToImage r)) := rfl

end FusionSystem
end Sharpness
