import Sharpness.Unconditional.SkeletonChainComparison
import Sharpness.Unconditional.RealizationUnitSkeletonMono
import Sharpness.Unconditional.RealizationUnitSkeletonChains
import Sharpness.RealizationUnitCochainNaturality

/-! Passage from the actual finite-dimensional skeletal unit maps to the
full realization-unit map. Stage quasi-isomorphisms, T1 separation and the
actual realized skeletal embeddings remain explicit geometric hypotheses.
No completed realization-unit theorem is asserted by this intermediate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable (R : Type u) [CommRing R] (X : SSet.{u})

def realizationSkeletonChainInclusion (n : ℕ) :
    (SingularCohomology.chainsFunctor R).obj |(X.skeleton n).toSSet| ⟶
      (SingularCohomology.chainsFunctor R).obj |X| :=
  (SingularCohomology.chainsFunctor R).map (SSet.toTop.map (X.skeleton n).ι)

theorem skeletonChainInclusion_degree_injective (n d : ℕ) :
    Function.Injective ((skeletonChainInclusion R X n).f d) := by
  letI : Mono ((skeletonChainInclusion R X n).f d) :=
    simplicialChainMap_degree_mono R (X.skeleton n).ι d
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- A source chain and a possible target bounding chain can be placed in
one actual skeleton. The target lift uses compactness; the source lift uses
the proved simplicial degree stabilization. -/
theorem realizationUnitSkeleton_pair_lift [T1Space |X|]
    (he : ∀ n, Topology.IsEmbedding (SSet.toTop.map (X.skeleton n).ι)) (d : ℕ)
    (x : (X.chainComplex (ModuleCat.of R R)).X d)
    (y : ((SingularCohomology.chainsFunctor R).obj |X|).X (d+1)) :
    ∃ n, ∃ xs : ((X.skeleton n).toSSet.chainComplex (ModuleCat.of R R)).X d,
      ∃ ys : ((SingularCohomology.chainsFunctor R).obj |(X.skeleton n).toSSet|).X (d+1),
        (skeletonChainInclusion R X n).f d xs = x ∧
          (realizationSkeletonChainInclusion R X n).f (d+1) ys = y := by
  obtain ⟨k, ys, hys⟩ := singularChain_factors_realizationSkeleton R X he (d+1) y
  let n := k+d+1
  have hkn : k ≤ n := by dsimp [n]; omega
  have hdn : d < n := by dsimp [n]; omega
  obtain ⟨xs, hxs⟩ := skeletonChainInclusion_surjective R X d n hdn x
  let transition := (SingularCohomology.chainsFunctor R).map
    ((realizationSkeletonDiagram X).map (homOfLE hkn))
  have hc : transition ≫ realizationSkeletonChainInclusion R X n =
      realizationSkeletonChainInclusion R X k := by
    change (SingularCohomology.chainsFunctor R).map
        ((realizationSkeletonDiagram X).map (homOfLE hkn)) ≫
      (SingularCohomology.chainsFunctor R).map ((realizationSkeletonCocone X).ι.app n) =
        (SingularCohomology.chainsFunctor R).map ((realizationSkeletonCocone X).ι.app k)
    rw [← (SingularCohomology.chainsFunctor R).map_comp, (realizationSkeletonCocone X).w]
  refine ⟨n, xs, transition.f (d+1) ys, hxs, ?_⟩
  exact (congrArg (fun f => (f.f (d+1)).hom ys) hc).trans hys

/-- Explicit final algebraic passage. The finite-skeleton and geometric
hypotheses must still be proved before this yields a realization-unit input. -/
theorem realizationUnitChainMap_quasiIso_of_skeleta [T1Space |X|]
    (he : ∀ n, Topology.IsEmbedding (SSet.toTop.map (X.skeleton n).ι))
    (hstage : ∀ n, QuasiIso (realizationUnitChainMap R (X.skeleton n).toSSet)) :
    QuasiIso (realizationUnitChainMap R X) := by
  apply SkeletonComparison.quasiIso_of_stage_chain_lifts
    (realizationUnitChainMap R X)
    (fun n => (X.skeleton n).toSSet.chainComplex (ModuleCat.of R R))
    (fun n => (SingularCohomology.chainsFunctor R).obj |(X.skeleton n).toSSet|)
    (skeletonChainInclusion R X) (realizationSkeletonChainInclusion R X)
    (fun n => realizationUnitChainMap R (X.skeleton n).toSSet)
  · intro n
    exact realizationUnitChainMap_naturality R (X.skeleton n).ι
  · exact skeletonChainInclusion_degree_injective R X
  · intro n d
    exact realizationSkeletonChainInclusion_degree_injective R X n (he n) d
  · exact hstage
  · exact singularChain_factors_realizationSkeleton R X he
  · exact realizationUnitSkeleton_pair_lift R X he

end Sharpness.RealizationUnitHomology
