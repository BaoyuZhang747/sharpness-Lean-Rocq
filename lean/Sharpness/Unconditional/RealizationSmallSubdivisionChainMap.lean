import Sharpness.Unconditional.RealizationUnitHomologySubdivisionChainMap
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! The actual small-singular inclusion is split injective in each degree.
The splitting is only degreewise: it keeps small generators and kills the
others. No chain-level retraction is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R] (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

def smallSingularChainsDegreeRetraction (n : ℕ) :
    ((SingularCohomology.chainsFunctor R).obj X).X n ⟶ (smallSingularChains X U R).X n := by
  classical
  exact Sigma.desc fun σ => if h : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌) then
    (singularSmallSubcomplex X U).toSSet.ιChainComplex (R := ModuleCat.of R R) ⟨σ, h⟩ else 0

theorem smallSingularChainsDegreeRetraction_id (n : ℕ) :
    (smallSingularChainsInclusion X U R).f n ≫ smallSingularChainsDegreeRetraction R X U n =
      𝟙 ((smallSingularChains X U R).X n) := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, smallSingularChainsInclusion_generator]
  change (Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) => ModuleCat.of R R) σ.1 ≫
    Sigma.desc _) = _
  rw [Sigma.ι_desc, dif_pos σ.2, Category.comp_id]
  rfl

def smallSingularChainsInclusionDegreeSplitMono (n : ℕ) :
    SplitMono ((smallSingularChainsInclusion X U R).f n) where
  retraction := smallSingularChainsDegreeRetraction R X U n
  id := smallSingularChainsDegreeRetraction_id R X U n

instance smallSingularChainsInclusion_degree_isSplitMono (n : ℕ) :
    IsSplitMono ((smallSingularChainsInclusion X U R).f n) :=
  IsSplitMono.mk' (smallSingularChainsInclusionDegreeSplitMono R X U n)

instance smallSingularChainsInclusion_degree_mono (n : ℕ) :
    Mono ((smallSingularChainsInclusion X U R).f n) := inferInstance

theorem smallSingularChainsInclusion_degree_injective (n : ℕ) :
    Function.Injective ((smallSingularChainsInclusion X U R).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

instance smallSingularChainsInclusion_mono : Mono (smallSingularChainsInclusion X U R) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

/-- Boundary commutation on small chains follows from the actual ambient
boundary equation, preservation, and the proved degreewise injection. -/
theorem smallSubdivisionDegree_boundary (n : ℕ) :
    smallSubdivisionDegree R X U (n + 1) ≫ (smallSingularChains X U R).d (n + 1) n =
      (smallSingularChains X U R).d (n + 1) n ≫ smallSubdivisionDegree R X U n := by
  apply (cancel_mono ((smallSingularChainsInclusion X U R).f n)).mp
  let j := smallSingularChainsInclusion X U R
  let C := (SingularCohomology.chainsFunctor R).obj X
  let S := smallSingularChains X U R
  change (smallSubdivisionDegree R X U (n + 1) ≫ S.d (n + 1) n) ≫ j.f n =
    (S.d (n + 1) n ≫ smallSubdivisionDegree R X U n) ≫ j.f n
  calc
    _ = smallSubdivisionDegree R X U (n + 1) ≫ (j.f (n + 1) ≫ C.d (n + 1) n) := by
      rw [Category.assoc, j.comm]
    _ = (j.f (n + 1) ≫ subdivisionDegree R X (n + 1)) ≫ C.d (n + 1) n := by
      rw [← Category.assoc, subdivisionDegree_preserves_small]
    _ = (j.f (n + 1) ≫ C.d (n + 1) n) ≫ subdivisionDegree R X n := by
      rw [Category.assoc, subdivisionDegree_boundary, ← Category.assoc]
    _ = S.d (n + 1) n ≫ (smallSubdivisionDegree R X U n ≫ j.f n) := by
      rw [j.comm, Category.assoc, subdivisionDegree_preserves_small]
    _ = _ := (Category.assoc _ _ _).symm

/-- Actual signed barycentric subdivision on the small-singular subcomplex. -/
def smallSubdivisionChainMap : smallSingularChains X U R ⟶ smallSingularChains X U R where
  f := smallSubdivisionDegree R X U
  comm' i j hij := by
    have h : i = j + 1 := hij.symm
    subst i
    exact smallSubdivisionDegree_boundary R X U j

theorem smallSubdivisionChainMap_inclusion :
    smallSubdivisionChainMap R X U ≫ smallSingularChainsInclusion X U R =
      smallSingularChainsInclusion X U R ≫ subdivisionChainMap R X := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact subdivisionDegree_preserves_small R X U n

@[simp] theorem smallSubdivisionDegree_zero : smallSubdivisionDegree R X U 0 = 𝟙 _ := by
  apply (cancel_mono ((smallSingularChainsInclusion X U R).f 0)).mp
  rw [subdivisionDegree_preserves_small, subdivisionDegree_zero, Category.comp_id,
    Category.id_comp]

end Sharpness.RealizationUnitHomology
