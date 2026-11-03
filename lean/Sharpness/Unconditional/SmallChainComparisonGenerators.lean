import Sharpness.Unconditional.SmallChainComparisonAlgebra
import Sharpness.Unconditional.RealizationSmallSubdivisionChainMap
import Sharpness.Unconditional.RealizationSubdivisionMeshSingular

/-! Actual singular-chain generators, powers of signed subdivision, and the
uniform geometric smallness bound. Finite-chain eventual smallness is deduced
from the universal property of the native free chain modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped BigOperators
variable (R : Type u) [CommRing R]

theorem chain_mem_submodule_of_generators (Y : SSet.{u}) (n : ℕ)
    (P : Submodule R ((Y.chainComplex (ModuleCat.of R R)).X n))
    (hP : ∀ σ : Y.obj (op ⦋n⦌), ∀ r : R, Y.ιChainComplex (R := ModuleCat.of R R) σ r ∈ P)
    (x : (Y.chainComplex (ModuleCat.of R R)).X n) : x ∈ P := by
  let toP : (Y.chainComplex (ModuleCat.of R R)).X n ⟶ ModuleCat.of R P :=
    Sigma.desc (fun σ => ModuleCat.ofHom ((Y.ιChainComplex (R := ModuleCat.of R R) σ).hom.codRestrict P (hP σ)))
  let fromP : ModuleCat.of R P ⟶ (Y.chainComplex (ModuleCat.of R R)).X n :=
    ModuleCat.ofHom P.subtype
  have he : toP ≫ fromP = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc]
    change (Sigma.ι (fun _ : Y.obj (op ⦋n⦌) => ModuleCat.of R R) σ ≫ Sigma.desc _) ≫ _ = _
    rw [Sigma.ι_desc, Category.comp_id]
    rfl
  have hx : (toP x : (Y.chainComplex (ModuleCat.of R R)).X n) = x :=
    congrArg (fun f => f.hom x) he
  exact hx ▸ (toP x).property

theorem singularIteratedBarycentricCell_append_singleton {X : TopCat.{u}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (p : Equiv.Perm (Fin (n+1))) (ps : List (Equiv.Perm (Fin (n+1)))) :
    singularIteratedBarycentricCell (singularBarycentricCell σ p) ps =
      singularIteratedBarycentricCell σ (ps ++ [p]) := by
  induction ps with
  | nil => simp [singularIteratedBarycentricCell_cons]
  | cons q ps ih =>
      rw [singularIteratedBarycentricCell_cons, List.cons_append,
        singularIteratedBarycentricCell_cons, ih]

variable (X : TopCat.{u})

theorem subdivisionDegree_generator_apply (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (r : R) :
    subdivisionDegree R X n ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ r) =
      ∑ p : Equiv.Perm (Fin (n+1)), (p.sign : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          (singularBarycentricCell σ p) r := by
  have h := congrArg (fun f => f.hom r) (subdivisionDegree_generator R X n σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply] using! h

theorem subdivisionDegree_pow_generator_mem (n k : ℕ)
    (P : Submodule R (((SingularCohomology.chainsFunctor R).obj X).X n))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hP : ∀ ps : List (Equiv.Perm (Fin (n+1))), ps.length=k → ∀ r : R,
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) (singularIteratedBarycentricCell σ ps) r ∈ P)
    (r : R) :
    ((subdivisionDegree R X n).hom^k) ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ r) ∈ P := by
  induction k generalizing σ with
  | zero => simpa using hP [] rfl r
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, subdivisionDegree_generator_apply, map_sum]
      apply P.sum_mem
      intro p _
      rw [map_zsmul]
      apply P.toAddSubgroup.zsmul_mem
      apply ih
      intro ps hps a
      rw [singularIteratedBarycentricCell_append_singleton]
      exact hP (ps ++ [p]) (by simp [hps]) a

variable {ι : Type v} (U : ι → Set X)

def smallChainImage (n : ℕ) :
    Submodule R (((SingularCohomology.chainsFunctor R).obj X).X n) :=
  LinearMap.range ((smallSingularChainsInclusion X U R).f n).hom

theorem smallChainImage_generator (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌)) (r : R) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ r ∈
      smallChainImage R X U n := by
  refine ⟨(singularSmallSubcomplex X U).toSSet.ιChainComplex (R := ModuleCat.of R R) ⟨σ, hσ⟩ r, ?_⟩
  exact congrArg (fun f => f.hom r) (smallSingularChainsInclusion_generator X U R n ⟨σ, hσ⟩)

theorem smallChainImage_subdivision (n : ℕ) (x : _)
    (hx : x ∈ smallChainImage R X U n) : subdivisionDegree R X n x ∈ smallChainImage R X U n := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨smallSubdivisionDegree R X U n y, ?_⟩
  exact congrArg (fun f => f.hom y) (subdivisionDegree_preserves_small R X U n)

theorem subdivisionDegree_eventually_small (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (x : ((SingularCohomology.chainsFunctor R).obj X).X n) :
    ∃ k : ℕ, ((subdivisionDegree R X n).hom^k) x ∈ smallChainImage R X U n := by
  let P := SmallChainComparison.eventualSubmodule (subdivisionDegree R X n).hom
    (smallChainImage R X U n) (smallChainImage_subdivision R X U n)
  change x ∈ P
  apply chain_mem_submodule_of_generators R (TopCat.toSSet.obj X) n P
  intro σ r
  obtain ⟨k, hk⟩ := singularIteratedBarycentricCell_eventually_small σ U hU
    (fun t => hcover (X.toSSetObjEquiv _ σ t))
  refine ⟨k, subdivisionDegree_pow_generator_mem R X n k _ σ ?_ r⟩
  intro ps hps a
  exact smallChainImage_generator R X U n _ (hk ps (by omega)) a

theorem subdivisionChainMap_pow_f_hom (k n : ℕ) :
    (((End.of (subdivisionChainMap R X))^k).f n).hom = (subdivisionDegree R X n).hom^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, End.mul_def, HomologicalComplex.comp_f, ModuleCat.hom_comp, ih]
      rfl

theorem subdivisionChainMap_eventually_small (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (x : ((SingularCohomology.chainsFunctor R).obj X).X n) :
    ∃ k : ℕ, ∃ y : (smallSingularChains X U R).X n,
      (smallSingularChainsInclusion X U R).f n y =
        ((End.of (subdivisionChainMap R X))^k).f n x := by
  obtain ⟨k, y, hy⟩ := subdivisionDegree_eventually_small R X U hU hcover n x
  refine ⟨k, y, ?_⟩
  change _ = ((((End.of (subdivisionChainMap R X))^k).f n).hom) x
  rw [subdivisionChainMap_pow_f_hom]
  exact hy

end Sharpness.RealizationUnitHomology


