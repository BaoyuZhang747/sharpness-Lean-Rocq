import Sharpness.Unconditional.RealizationUnitSkeletonFiniteChains
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Injectivity of the actual chain maps of embedded filtration stages.
This supplies cancellation for finite-stage cycle and boundary passage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

theorem simplicialChainMap_degree_mono (R : Type u) [CommRing R]
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : ℕ) :
    Mono ((SSet.chainComplexMap f (ModuleCat.of R R)).f d) := by
  change Mono ((sigmaConst.obj (ModuleCat.of R R)).map (f.app (op ⦋d⦌)))
  infer_instance

theorem singularChainMap_degree_injective (R : Type u) [CommRing R]
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Function.Injective f) (d : ℕ) :
    Function.Injective (((SingularCohomology.chainsFunctor R).map f).f d) := by
  letI : Mono f := (TopCat.mono_iff_injective f).mpr hf
  letI : Mono (TopCat.toSSet.map f) := inferInstance
  letI : Mono (((SingularCohomology.chainsFunctor R).map f).f d) :=
    simplicialChainMap_degree_mono R (TopCat.toSSet.map f) d
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem realizationSkeletonChainInclusion_degree_injective (R : Type u) [CommRing R]
    (X : SSet.{u}) (n : ℕ) (he : Topology.IsEmbedding (SSet.toTop.map (X.skeleton n).ι))
    (d : ℕ) :
    Function.Injective (((SingularCohomology.chainsFunctor R).map
      (SSet.toTop.map (X.skeleton n).ι)).f d) :=
  singularChainMap_degree_injective R _ he.injective d

end Sharpness.RealizationUnitHomology
