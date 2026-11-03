import Sharpness.Unconditional.RealizationUnitHomologySubdivisionGeometry

/-! Explicit signed barycentric subdivision operators in each degree. The
boundary-commutation and chain-homotopy proofs are separate obligations; these
degree maps are not packaged as a chain map before those are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped BigOperators

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- The usual signed sum over actual barycentric cells of a singular simplex. -/
def subdivisionDegree (n : ℕ) :
    ((SingularCohomology.chainsFunctor R).obj X).X n ⟶
      ((SingularCohomology.chainsFunctor R).obj X).X n :=
  Sigma.desc fun (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) => ∑ p : Equiv.Perm (Fin (n + 1)),
    (p.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
      (singularBarycentricCell σ p)

@[reassoc] theorem subdivisionDegree_generator (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ ≫
        subdivisionDegree R X n =
      ∑ p : Equiv.Perm (Fin (n + 1)),
        (p.sign : ℤ) • (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          (singularBarycentricCell σ p) :=
  Sigma.ι_desc _ _

@[simp] theorem singularBarycentricCell_zero
    (σ : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) (p : Equiv.Perm (Fin 1)) :
    singularBarycentricCell σ p = σ := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change X.toSSetObjEquiv _ (singularAffinePull σ (prefixBarycenter p)) t =
    X.toSSetObjEquiv _ σ t
  rw [singularAffinePull_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual subdivision degree operator fixes every zero-chain. -/
@[simp] theorem subdivisionDegree_zero : subdivisionDegree R X 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [subdivisionDegree_generator]
  erw [Category.comp_id]
  have hp (p : Equiv.Perm (Fin 1)) : p = 1 := Subsingleton.elim _ _
  letI : Unique (Equiv.Perm (Fin 1)) := { default := 1, uniq := hp }
  simp only [hp, map_one, Units.val_one, one_zsmul, singularBarycentricCell_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul]

variable {ι : Type v} (U : ι → Set X)

/-- The same signed sum on the actual small-singular chain subcomplex. -/
def smallSubdivisionDegree (n : ℕ) :
    (smallSingularChains X U R).X n ⟶ (smallSingularChains X U R).X n :=
  Sigma.desc fun (σ : (singularSmallSubcomplex X U).obj (op ⦋n⦌)) =>
    ∑ p : Equiv.Perm (Fin (n + 1)),
    (p.sign : ℤ) • (singularSmallSubcomplex X U).toSSet.ιChainComplex
      (R := ModuleCat.of R R)
      ⟨singularBarycentricCell σ.1 p, singularBarycentricCell_mem U σ.1 σ.2 p⟩

@[reassoc] theorem smallSubdivisionDegree_generator (n : ℕ)
    (σ : (singularSmallSubcomplex X U).obj (op ⦋n⦌)) :
    (singularSmallSubcomplex X U).toSSet.ιChainComplex (R := ModuleCat.of R R) σ ≫
        smallSubdivisionDegree R X U n =
      ∑ p : Equiv.Perm (Fin (n + 1)),
        (p.sign : ℤ) • (singularSmallSubcomplex X U).toSSet.ιChainComplex
          (R := ModuleCat.of R R)
          ⟨singularBarycentricCell σ.1 p, singularBarycentricCell_mem U σ.1 σ.2 p⟩ :=
  Sigma.ι_desc _ _

/-- Actual subdivision degree operators preserve every small-singular chain
subcomplex, before any openness or cover condition is imposed. -/
theorem subdivisionDegree_preserves_small (n : ℕ) :
    smallSubdivisionDegree R X U n ≫ (smallSingularChainsInclusion X U R).f n =
      (smallSingularChainsInclusion X U R).f n ≫ subdivisionDegree R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  simp only [← Category.assoc, smallSubdivisionDegree_generator,
    smallSingularChainsInclusion_generator, subdivisionDegree_generator,
    Preadditive.sum_comp, Preadditive.zsmul_comp]

end Sharpness.RealizationUnitHomology
