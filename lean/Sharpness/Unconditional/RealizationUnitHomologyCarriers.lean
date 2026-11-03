import Sharpness.Unconditional.RealizationUnitHomologyNaturalHomotopy
import Sharpness.Unconditional.RealizationUnitHomologySmallChains

/-! Every natural map between degrees of the actual singular-chain functor
preserves the carrier of each simplex, and hence all small-chain subcomplexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Set X) {n : ℕ}

/-- Every singular simplex of a small simplex's source stays in its carrier. -/
theorem singularSimplex_carrier (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌)) :
    SSet.Subcomplex.range (TopCat.toSSet.map σ.down) ≤ singularSmallSubcomplex X U := by
  intro m τ hτ
  obtain ⟨υ, rfl⟩ := hτ
  obtain ⟨i, hi⟩ := hσ
  refine ⟨i, fun t => ?_⟩
  let υ' : SimplexCategory.toTop.{u}.obj m.unop ⟶
      SimplexCategory.toTop.{u}.obj ⦋n⦌ := υ.down
  exact hi (υ' ⟨t⟩).down

/-- The actual singular map of a small simplex, with its codomain restricted. -/
def singularSimplexSmallMap (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌)) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) ⟶
      (singularSmallSubcomplex X U).toSSet :=
  SSet.Subcomplex.lift (TopCat.toSSet.map σ.down) (singularSimplex_carrier U σ hσ)

variable (R : Type u) [CommRing R]

def singularSimplexSmallChainMap (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌)) :
    (SingularCohomology.chainsFunctor R).obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) ⟶
      smallSingularChains X U R :=
  SSet.chainComplexMap (singularSimplexSmallMap U σ hσ) (ModuleCat.of R R)

theorem singularSimplexSmallChainMap_inclusion
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (singularSmallSubcomplex X U).obj (op ⦋n⦌)) :
    singularSimplexSmallChainMap U R σ hσ ≫ smallSingularChainsInclusion X U R =
      (SingularCohomology.chainsFunctor R).map σ.down := by
  change ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map _ =
    ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- Restrict a natural degree map by transporting its value on the identity
model simplex through each actual small simplex. -/
def smallNaturalDegree {m : ℕ}
    (τ : SingularCohomology.chainsFunctor R ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⟶
      SingularCohomology.chainsFunctor R ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) m) :
    (smallSingularChains X U R).X n ⟶ (smallSingularChains X U R).X m :=
  Sigma.desc fun (σ : (singularSmallSubcomplex X U).obj (op ⦋n⦌)) =>
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
      (R := ModuleCat.of R R) (ULift.up (𝟙 (SimplexCategory.toTop.{u}.obj ⦋n⦌))) ≫
    τ.app (SimplexCategory.toTop.{u}.obj ⦋n⦌) ≫
    (singularSimplexSmallChainMap U R σ.val σ.property).f m

theorem smallNaturalDegree_inclusion {m : ℕ}
    (τ : SingularCohomology.chainsFunctor R ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⟶
      SingularCohomology.chainsFunctor R ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) m) :
    smallNaturalDegree U R τ ≫ (smallSingularChainsInclusion X U R).f m =
      (smallSingularChainsInclusion X U R).f n ≫ τ.app X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  simp only [← Category.assoc, smallSingularChainsInclusion_generator]
  change _ = (TopCat.toSSet.obj X).ιChainComplex σ.val ≫ _
  simp only [smallNaturalDegree, SSet.ιChainComplex, Sigma.ι_desc]
  have hi := congrArg (fun f => f.f m)
    (singularSimplexSmallChainMap_inclusion U R σ.val σ.property)
  change (singularSimplexSmallChainMap U R σ.val σ.property).f m ≫
    (smallSingularChainsInclusion X U R).f m =
      ((SingularCohomology.chainsFunctor R).map σ.val.down).f m at hi
  rw [Category.assoc, Category.assoc, hi]
  have hn : ((SingularCohomology.chainsFunctor R).map σ.val.down).f n ≫ τ.app X =
      τ.app (SimplexCategory.toTop.{u}.obj ⦋n⦌) ≫
        ((SingularCohomology.chainsFunctor R).map σ.val.down).f m := τ.naturality σ.val.down
  rw [← hn]
  rw [← Category.assoc]
  have hg : (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
        (R := ModuleCat.of R R) (ULift.up (𝟙 (SimplexCategory.toTop.{u}.obj ⦋n⦌))) ≫
      ((SingularCohomology.chainsFunctor R).map σ.val.down).f n =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ.val := by
    erw [SSet.ι_chainComplexMap_f]
    congr 1
  exact congrArg (fun f => f ≫ τ.app X) hg

end Sharpness.RealizationUnitHomology
