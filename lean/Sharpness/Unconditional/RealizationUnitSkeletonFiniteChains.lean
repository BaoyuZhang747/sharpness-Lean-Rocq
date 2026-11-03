import Sharpness.Unconditional.RealizationUnitSkeletonCompact
import Sharpness.SingularCochains
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-! Actual finite-stage factorization of continuous simplices and chains.
Embedding and T1 hypotheses remain explicit until supplied by the geometric
realization attachment argument. No singular-colimit preservation is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set

theorem continuousMap_factors_sequentialColimit (F : ℕ ⥤ TopCat.{u})
    (c : Cocone F) (hc : IsColimit c) [T1Space c.pt]
    (he : ∀ n, Topology.IsEmbedding (c.ι.app n))
    {Z : Type v} [TopologicalSpace Z] [CompactSpace Z] (σ : C(Z, c.pt)) :
    ∃ n, ∃ τ : C(Z, F.obj n), (c.ι.app n).hom.comp τ = σ := by
  classical
  obtain ⟨n, hn⟩ := compact_subset_sequentialColimit F c hc (isCompact_range σ.continuous)
  have hpre : ∀ z, ∃ y, c.ι.app n y = σ z := fun z => hn ⟨z, rfl⟩
  choose τ hτ using hpre
  have hτcont : Continuous τ := (he n).continuous_iff.mpr (by
    have heq : (fun x => c.ι.app n (τ x)) = σ := funext hτ
    change Continuous (fun x => c.ι.app n (τ x))
    rw [heq]
    exact σ.continuous)
  exact ⟨n, ⟨τ, hτcont⟩, ContinuousMap.ext hτ⟩

theorem singularSimplex_factors_sequentialColimit (F : ℕ ⥤ TopCat.{u})
    (c : Cocone F) (hc : IsColimit c) [T1Space c.pt]
    (he : ∀ n, Topology.IsEmbedding (c.ι.app n)) (d : ℕ)
    (σ : (TopCat.toSSet.obj c.pt).obj (op ⦋d⦌)) :
    ∃ n, ∃ τ : (TopCat.toSSet.obj (F.obj n)).obj (op ⦋d⦌),
      (TopCat.toSSet.map (c.ι.app n)).app (op ⦋d⦌) τ = σ := by
  obtain ⟨n, τ, hτ⟩ := continuousMap_factors_sequentialColimit F c hc he
    (c.pt.toSSetObjEquiv (op ⦋d⦌) σ)
  refine ⟨n, ((F.obj n).toSSetObjEquiv (op ⦋d⦌)).symm τ, ?_⟩
  apply (c.pt.toSSetObjEquiv (op ⦋d⦌)).injective
  change (c.ι.app n).hom.comp
    ((F.obj n).toSSetObjEquiv _ (((F.obj n).toSSetObjEquiv _).symm τ)) = _
  rw [Equiv.apply_symm_apply]
  exact hτ

private theorem chainDegree_submodule_eq_top (R : Type u) [CommRing R]
    (X : SSet.{u}) (d : ℕ) (P : Submodule R ((X.chainComplex (ModuleCat.of R R)).X d))
    (hP : ∀ (σ : X.obj (op ⦋d⦌)) (r : R),
      (X.ιChainComplex (R := ModuleCat.of R R) σ) r ∈ P) : P = ⊤ := by
  have hq : ModuleCat.ofHom P.mkQ = (0 : (X.chainComplex (ModuleCat.of R R)).X d ⟶
      ModuleCat.of R (_ ⧸ P)) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change P.mkQ ((X.ιChainComplex (R := ModuleCat.of R R) σ) r) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hP σ r)
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero P).mp
  exact congrArg (fun f : (X.chainComplex (ModuleCat.of R R)).X d ⟶
    ModuleCat.of R (_ ⧸ P) => f z) hq

/-- Directed images of simplicial stages contain every finite chain once
they contain every actual simplex generator. -/
theorem chainDegree_factors_sequential (R : Type u) [CommRing R]
    (F : ℕ ⥤ SSet.{u}) (c : Cocone F) (d : ℕ)
    (hσ : ∀ σ : c.pt.obj (op ⦋d⦌),
      ∃ n, ∃ τ : (F.obj n).obj (op ⦋d⦌), (c.ι.app n).app (op ⦋d⦌) τ = σ)
    (z : (c.pt.chainComplex (ModuleCat.of R R)).X d) :
    ∃ n, ∃ y : ((F.obj n).chainComplex (ModuleCat.of R R)).X d,
      (SSet.chainComplexMap (c.ι.app n) (ModuleCat.of R R)).f d y = z := by
  let J := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let M : ℕ → Submodule R ((c.pt.chainComplex (ModuleCat.of R R)).X d) :=
    fun n => LinearMap.range ((J.map (c.ι.app n)).f d).hom
  have hmono : Monotone M := by
    intro n m hnm z hz
    obtain ⟨y, rfl⟩ := hz
    refine ⟨(J.map (F.map (homOfLE hnm))).f d y, ?_⟩
    have hmap : J.map (F.map (homOfLE hnm)) ≫ J.map (c.ι.app m) = J.map (c.ι.app n) := by
      rw [← J.map_comp, c.w]
    exact congrArg (fun f => f.f d y) hmap
  have htop : (⨆ n, M n) = ⊤ := by
    apply chainDegree_submodule_eq_top R c.pt d
    intro σ r
    obtain ⟨n, τ, rfl⟩ := hσ σ
    apply (le_iSup M n)
    refine ⟨((F.obj n).ιChainComplex (R := ModuleCat.of R R) τ) r, ?_⟩
    exact congrArg (fun f : ModuleCat.of R R ⟶ (c.pt.chainComplex (ModuleCat.of R R)).X d => f r)
      (SSet.ι_chainComplexMap_f _ _ (c.ι.app n) (ModuleCat.of R R) τ)
  have hz : z ∈ ⨆ n, M n := by rw [htop]; trivial
  obtain ⟨n, y, hy⟩ := (Submodule.mem_iSup_of_directed M hmono.directed_le).mp hz
  exact ⟨n, y, hy⟩

/-- Every singular chain in an actual sequential colimit of embedded stages
comes from one stage. Compact simplex factorization and finite chain support
are both proved above, rather than packaged as a colimit-preservation input. -/
theorem singularChain_factors_sequentialColimit (R : Type u) [CommRing R]
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c) [T1Space c.pt]
    (he : ∀ n, Topology.IsEmbedding (c.ι.app n)) (d : ℕ)
    (z : ((SingularCohomology.chainsFunctor R).obj c.pt).X d) :
    ∃ n, ∃ y : ((SingularCohomology.chainsFunctor R).obj (F.obj n)).X d,
      ((SingularCohomology.chainsFunctor R).map (c.ι.app n)).f d y = z :=
  chainDegree_factors_sequential R (F ⋙ TopCat.toSSet) (TopCat.toSSet.mapCocone c) d
    (singularSimplex_factors_sequentialColimit F c hc he d) z

/-- Actual finite-chain passage through realized skeleta, once their
geometric separation and embedding properties have been established. -/
theorem singularChain_factors_realizationSkeleton (R : Type u) [CommRing R]
    (X : SSet.{u}) [T1Space |X|]
    (he : ∀ n, Topology.IsEmbedding (SSet.toTop.map (X.skeleton n).ι)) (d : ℕ)
    (z : ((SingularCohomology.chainsFunctor R).obj |X|).X d) :
    ∃ n, ∃ y : ((SingularCohomology.chainsFunctor R).obj |(X.skeleton n).toSSet|).X d,
      ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map (X.skeleton n).ι)).f d y = z := by
  letI : T1Space (realizationSkeletonCocone X).pt := inferInstanceAs (T1Space |X|)
  exact singularChain_factors_sequentialColimit R (realizationSkeletonDiagram X)
    (realizationSkeletonCocone X) (realizationSkeletonIsColimit X) he d z

end Sharpness.RealizationUnitHomology
