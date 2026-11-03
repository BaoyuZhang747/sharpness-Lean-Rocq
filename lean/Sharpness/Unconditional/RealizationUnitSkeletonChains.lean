import Sharpness.Unconditional.RealizationUnitSkeleton
import Mathlib.Algebra.Homology.QuasiIso

/-! Actual simplicial chain and homology stabilization along skeleta. This
uses degreewise equality of simplex sets; no topological compact-image or
singular-chain colimit statement is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R] (X : SSet.{u})

def skeletonChainInclusion (n : ℕ) :
    (X.skeleton n).toSSet.chainComplex (ModuleCat.of R R) ⟶ X.chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap (X.skeleton n).ι (ModuleCat.of R R)

/-- Every actual simplicial chain in degree `d` comes from stage `d+1`.
This does not require a finiteness restriction on the simplicial set. -/
theorem skeletonChainInclusion_surjective (d n : ℕ) (h : d < n) :
    Function.Surjective ((skeletonChainInclusion R X n).f d) := by
  letI : IsIso ((skeletonChainInclusion R X n).f d) :=
    skeletonChainInclusion_degree_isIso R X d n h
  intro z
  refine ⟨(inv ((skeletonChainInclusion R X n).f d)) z, ?_⟩
  exact congrArg (fun f : (X.chainComplex (ModuleCat.of R R)).X d ⟶
    (X.chainComplex (ModuleCat.of R R)).X d => f z)
      (IsIso.inv_hom_id ((skeletonChainInclusion R X n).f d))

private theorem down_prev_nat (d : ℕ) : (ComplexShape.down ℕ).prev d = d + 1 :=
  ComplexShape.prev_eq' _ rfl

private theorem down_next_nat_le (d : ℕ) : (ComplexShape.down ℕ).next d ≤ d := by
  cases d with
  | zero =>
    rw [ComplexShape.next_eq_self' _ 0 (by intro k; change ¬ k + 1 = 0; omega)]
  | succ d =>
    rw [ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (d + 1) d from rfl)]
    omega

/-- Simplicial homology in degree `d` is already stable in every skeleton
containing dimensions through `d+1`. -/
theorem skeletonChainInclusion_quasiIsoAt (d n : ℕ) (h : d + 1 < n) :
    QuasiIsoAt (skeletonChainInclusion R X n) d := by
  let f := skeletonChainInclusion R X n
  haveI h₁ : IsIso (f.f ((ComplexShape.down ℕ).prev d)) :=
    skeletonChainInclusion_degree_isIso R X _ n (by rw [down_prev_nat]; exact h)
  haveI h₂ : IsIso (f.f d) := skeletonChainInclusion_degree_isIso R X d n (by omega)
  haveI h₃ : IsIso (f.f ((ComplexShape.down ℕ).next d)) :=
    skeletonChainInclusion_degree_isIso R X _ n
      (lt_of_le_of_lt (down_next_nat_le d) (by omega))
  rw [quasiIsoAt_iff]
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
    (ComplexShape.down ℕ) d).map f
  haveI : IsIso φ.τ₁ := h₁
  haveI : IsIso φ.τ₂ := h₂
  haveI : IsIso φ.τ₃ := h₃
  haveI : IsIso φ := ShortComplex.isIso_of_isIso φ
  exact ShortComplex.quasiIso_of_isIso φ

def skeletonHomologyIso (d n : ℕ) (h : d + 1 < n) :
    ((X.skeleton n).toSSet.chainComplex (ModuleCat.of R R)).homology d ≅
      (X.chainComplex (ModuleCat.of R R)).homology d := by
  letI := skeletonChainInclusion_quasiIsoAt R X d n h
  exact isoOfQuasiIsoAt (skeletonChainInclusion R X n) d

end Sharpness.RealizationUnitHomology
