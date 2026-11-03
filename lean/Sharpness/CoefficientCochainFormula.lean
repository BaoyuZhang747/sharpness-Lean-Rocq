import Sharpness.CoefficientReplacement
import Sharpness.AlternatingCofaceFunctorIso

/-! The coboundary formula for the actual coefficient complex. It is
the sum of the actual head-arrow pullback and the signed deleted-vertex
terms, indexed by the actual simplex cofaces. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory Simplicial Opposite

theorem piModule_zsmul_sum_apply {I : Type v} {J : Type w} [Fintype J] {A : I → Type u}
    [∀ i, AddCommGroup (A i)] (f : J → ∀ i, A i) (a : J → ℤ) (i : I) :
    (∑ j, a j • f j) i = ∑ j, a j • f j i := by
  simp only [Finset.sum_apply, Pi.smul_apply]

variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem coefficientCochains_d_apply (n : ℕ) (x : (coefficientCochains M).X n)
    (s : ComposableArrows C (n+1)) :
    (coefficientCochains M).d n (n+1) x s =
      ∑ i : Fin (n+2), (-1 : ℤ)^(i : ℕ) •
        M.map (categoryChainHeadArrow (SimplexCategory.δ i) s).op
          (x (restrictCategoryChain (SimplexCategory.δ i) s)) := by
  have h := congrArg (fun f => f x s) (alternatingCoface_d (coefficientReplacement M) n)
  change (((coefficientCochains M).d n (n+1)).hom x) s =
    ((∑ i : Fin (n+2), (-1 : ℤ)^(i : ℕ) • (coefficientReplacement M).δ i).hom x) s at h
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply] at h
  exact h.trans (piModule_zsmul_sum_apply
    (fun i : Fin (n+2) => ((coefficientReplacement M).δ i).hom x)
    (fun i => (-1 : ℤ)^(i : ℕ)) s)

end Sharpness
