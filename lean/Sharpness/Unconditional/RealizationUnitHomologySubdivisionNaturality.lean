import Sharpness.Unconditional.RealizationUnitHomologySubdivisionOperators

/-! Naturality of the actual signed subdivision operators in each degree.
Their chain-map equation is a separate combinatorial statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped BigOperators

@[simp] theorem singularAffinePull_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {n m : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋m⦌))
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    (TopCat.toSSet.map f).app (op ⦋n⦌) (singularAffinePull σ v) =
      singularAffinePull ((TopCat.toSSet.map f).app (op ⦋m⦌) σ) v := by
  apply (Y.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rfl

@[simp] theorem singularBarycentricCell_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (p : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.map f).app (op ⦋n⦌) (singularBarycentricCell σ p) =
      singularBarycentricCell ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) p :=
  singularAffinePull_naturality f σ (prefixBarycenter p)

variable (R : Type u) [CommRing R]

/-- Every continuous map commutes with actual subdivision in every degree. -/
theorem subdivisionDegree_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((SingularCohomology.chainsFunctor R).map f).f n ≫ subdivisionDegree R Y n =
      subdivisionDegree R X n ≫ ((SingularCohomology.chainsFunctor R).map f).f n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have hi (τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) τ ≫
        ((SingularCohomology.chainsFunctor R).map f).f n =
      (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R)
        ((TopCat.toSSet.map f).app (op ⦋n⦌) τ) :=
    SSet.ι_chainComplexMap_f _ _ _ _ _
  simp only [← Category.assoc, hi, subdivisionDegree_generator,
    Preadditive.sum_comp, Preadditive.zsmul_comp, singularBarycentricCell_naturality]

/-- The genuine degreewise natural transformation underlying subdivision. -/
def subdivisionDegreeNatTrans (n : ℕ) :
    SingularCohomology.chainsFunctor R ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⟶
    SingularCohomology.chainsFunctor R ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n where
  app X := subdivisionDegree R X n
  naturality {X Y} f := subdivisionDegree_naturality R f n

end Sharpness.RealizationUnitHomology
