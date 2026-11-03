import Sharpness.Unconditional.SmallChainComparisonGenerators
import Sharpness.Unconditional.RealizationUnitHomologySmallHomotopy

/-! The actual inclusion of small singular chains for an arbitrary open cover
is a quasi-isomorphism. Signed barycentric subdivision, both homotopies, and
eventual smallness of every finite chain are proved, not supplied as inputs. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory
variable (R : Type u) [CommRing R] (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

theorem smallSingularChainsInclusion_quasiIso (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (smallSingularChainsInclusion X U R) :=
  SmallChainComparison.quasiIso_of_eventual_image
    (smallSingularChainsInclusion X U R)
    (smallSingularChainsInclusion_degree_injective R X U)
    (End.of (smallSubdivisionChainMap R X U)) (End.of (subdivisionChainMap R X))
    (smallSubdivisionChainMap_inclusion R X U)
    (smallSubdivisionHomotopy R X U) (subdivisionHomotopy R X)
    (subdivisionChainMap_eventually_small R X U hU hcover)

/-- One depth works simultaneously for finitely many actual chains, at every later depth. -/
theorem subdivisionChainMap_eventually_small_finset (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (s : Finset (((SingularCohomology.chainsFunctor R).obj X).X n)) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ x ∈ s, ∃ y : (smallSingularChains X U R).X n,
      (smallSingularChainsInclusion X U R).f n y =
        ((End.of (subdivisionChainMap R X))^k).f n x := by
  obtain ⟨N, hN⟩ := SmallChainComparison.eventually_mem_finset
    (subdivisionDegree R X n).hom (smallChainImage R X U n)
    (smallChainImage_subdivision R X U n) s
    (fun x _ => subdivisionDegree_eventually_small R X U hU hcover n x)
  refine ⟨N, ?_⟩
  intro k hk x hx
  obtain ⟨y, hy⟩ := hN k hk x hx
  refine ⟨y, ?_⟩
  change _ = ((((End.of (subdivisionChainMap R X))^k).f n).hom) x
  rw [subdivisionChainMap_pow_f_hom]
  exact hy

end Sharpness.RealizationUnitHomology
