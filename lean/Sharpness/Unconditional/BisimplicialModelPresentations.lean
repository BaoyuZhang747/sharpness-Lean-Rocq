import Sharpness.Unconditional.BisimplicialModelAdjunction
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyNaturality
import Sharpness.Unconditional.ModelwisePresentationCoproduct
import Sharpness.Unconditional.FunctorChainTransposition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Actual degreewise model generators for diagonal and total bisimplicial
chains.  The presentations are induced by the representable adjunction and
the finite coproduct decomposition of each total degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Simplicial Opposite

variable (R : Type u) [CommRing R]

def bisimplicialDiagonalChainsFunctor :
    SimplicialObject SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  Functor.uncurry ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategoryᵒᵖ) ⋙
    simplicialChainsFunctor R

def bisimplicialChainBicomplexFunctor :
    SimplicialObject SSet.{u} ⥤
      HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (Functor.whiskeringRight _ _ _).obj (simplicialChainsFunctor R) ⋙
    AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)

def bisimplicialTotalChainsFunctor :
    SimplicialObject SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  bisimplicialChainBicomplexFunctor R ⋙
    HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.down ℕ)

@[simp] theorem bisimplicialDiagonalChainsFunctor_obj (X : SimplicialObject SSet.{u}) :
    (bisimplicialDiagonalChainsFunctor R).obj X = bisimplicialDiagonalChains X R := rfl

@[simp] theorem bisimplicialDiagonalChainsFunctor_map {X Y : SimplicialObject SSet.{u}}
    (φ : X ⟶ Y) :
    (bisimplicialDiagonalChainsFunctor R).map φ = bisimplicialDiagonalChainsMap φ R := rfl

@[simp] theorem bisimplicialTotalChainsFunctor_obj (X : SimplicialObject SSet.{u}) :
    (bisimplicialTotalChainsFunctor R).obj X = bisimplicialTotalChains X R := rfl

@[simp] theorem bisimplicialTotalChainsFunctor_map {X Y : SimplicialObject SSet.{u}}
    (φ : X ⟶ Y) :
    (bisimplicialTotalChainsFunctor R).map φ = bisimplicialTotalChainsMap φ R := rfl

def bisimplicialBidegreeModule (p q : ℕ) : SimplicialObject SSet.{u} ⥤ ModuleCat.{u} R :=
  (bisimplicialDegreeFunctor (ModuleCat.{u} R) p q).obj (ModuleCat.of R R)

def bisimplicialBidegreePresentation (p q : ℕ) :
    ModelPresentation (bisimplicialBidegreeModule R p q)
      (fun _ : Unit => bisimplicialRepresentable.{u} p q) :=
  ModelPresentation.ofAdjunction _ _ (bisimplicialDegreeAdjunction (ModuleCat.{u} R) p q)

theorem bisimplicialBidegreePresentation_generator (p q : ℕ) :
    (bisimplicialBidegreePresentation R p q).generator () =
      (Sigma.ι (fun _ : ((bisimplicialRepresentable.{u} p q).obj (op ⦋p⦌)).obj (op ⦋q⦌) =>
        ModuleCat.of R R) (bisimplicialRepresentableGenerator p q)) (1 : R) := rfl

def bisimplicialDiagonalDegree (n : ℕ) : SimplicialObject SSet.{u} ⥤ ModuleCat.{u} R :=
  bisimplicialDiagonalChainsFunctor R ⋙ HomologicalComplex.eval _ _ n

def bisimplicialTotalDegree (n : ℕ) : SimplicialObject SSet.{u} ⥤ ModuleCat.{u} R :=
  bisimplicialTotalChainsFunctor R ⋙ HomologicalComplex.eval _ _ n

def bisimplicialDiagonalDegreePresentation (n : ℕ) :
    ModelPresentation (bisimplicialDiagonalDegree R n)
      (fun _ : Unit => bisimplicialRepresentable.{u} n n) :=
  bisimplicialBidegreePresentation R n n

def bisimplicialTotalDegreeInclusion (n : ℕ) (i : Fin (n + 1)) :
    bisimplicialBidegreeModule R i.val (n - i.val) ⟶ bisimplicialTotalDegree R n where
  app X := (bisimplicialChainBicomplex X R).ιTotal (ComplexShape.down ℕ)
    i.val (n - i.val) n (by change i.val + (n - i.val) = n; omega)
  naturality {X Y} φ := by
    exact (HomologicalComplex₂.ιTotal_map (bisimplicialChainBicomplex X R)
      (bisimplicialChainBicomplex Y R) (bisimplicialChainBicomplexMap φ R)
      (ComplexShape.down ℕ) i.val (n - i.val) n
        (by change i.val + (n - i.val) = n; omega)).symm

def bisimplicialTotalDegreeProjection (n : ℕ) (i : Fin (n + 1)) :
    bisimplicialTotalDegree R n ⟶ bisimplicialBidegreeModule R i.val (n - i.val) where
  app X := chainTotalProjection (bisimplicialChainBicomplex X R) i.val (n - i.val) n
    (by omega)
  naturality {X Y} φ := by
    exact chainTotalMap_projection (bisimplicialChainBicomplex X R)
      (bisimplicialChainBicomplex Y R) (bisimplicialChainBicomplexMap φ R)
      i.val (n - i.val) n (by omega)

theorem bisimplicialTotalDegree_inclusion_projection (n : ℕ) (i : Fin (n + 1)) :
    bisimplicialTotalDegreeInclusion R n i ≫ bisimplicialTotalDegreeProjection R n i = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  exact chainTotalProjection_inclusion (bisimplicialChainBicomplex X R)
    i.val (n - i.val) n (by omega)

theorem bisimplicialTotalDegree_inclusion_projection_other (n : ℕ)
    (i j : Fin (n + 1)) (h : i ≠ j) :
    bisimplicialTotalDegreeInclusion R n i ≫ bisimplicialTotalDegreeProjection R n j = 0 := by
  apply NatTrans.ext
  funext X
  exact chainTotalProjection_other (bisimplicialChainBicomplex X R)
    j.val (n - j.val) n i.val (n - i.val) (by omega) (by omega)
      (fun he => h (Fin.ext he))

theorem bisimplicialTotalDegree_projection_sum (n : ℕ) :
    (∑ i : Fin (n + 1), bisimplicialTotalDegreeProjection R n i ≫
      bisimplicialTotalDegreeInclusion R n i) = 𝟙 (bisimplicialTotalDegree R n) := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app]
  change (∑ i : Fin (n + 1),
    chainTotalProjection (bisimplicialChainBicomplex X R) i.val (n - i.val) n (by omega) ≫
      (bisimplicialChainBicomplex X R).ιTotal (ComplexShape.down ℕ)
        i.val (n - i.val) n (by change i.val + (n - i.val) = n; omega)) = 𝟙 _
  exact chainTotal_projection_sum (bisimplicialChainBicomplex X R) n

/-- Each actual total degree is the finite coproduct of its bidegrees. -/
def bisimplicialTotalDegreeCoproductIso (n : ℕ) :
    (∐ fun i : Fin (n + 1) => bisimplicialBidegreeModule R i.val (n - i.val)) ≅
      bisimplicialTotalDegree R n where
  hom := Sigma.desc (bisimplicialTotalDegreeInclusion R n)
  inv := ∑ i : Fin (n + 1), bisimplicialTotalDegreeProjection R n i ≫
    Sigma.ι (fun j : Fin (n + 1) => bisimplicialBidegreeModule R j.val (n - j.val)) i
  hom_inv_id := by
    classical
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc, comp_sum, Category.comp_id]
    rw [Finset.sum_eq_single i]
    · rw [← Category.assoc, bisimplicialTotalDegree_inclusion_projection, Category.id_comp]
    · intro j _ hji
      rw [← Category.assoc,
        bisimplicialTotalDegree_inclusion_projection_other R n i j (Ne.symm hji), zero_comp]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  inv_hom_id := by
    simp only [sum_comp, Category.assoc, Sigma.ι_desc]
    exact bisimplicialTotalDegree_projection_sum R n

/-- The total degree is presented by the actual representable model in each
bidegree, with no homological condition included in the freeness data. -/
def bisimplicialTotalDegreePresentation (n : ℕ) :
    ModelPresentation (bisimplicialTotalDegree R n)
      (fun i : Fin (n + 1) => bisimplicialRepresentable.{u} i.val (n - i.val)) :=
  (ModelPresentation.coproductSingleton
    (fun i : Fin (n + 1) => bisimplicialBidegreeModule R i.val (n - i.val))
    (fun i => bisimplicialRepresentable.{u} i.val (n - i.val))
    (fun i => bisimplicialBidegreePresentation R i.val (n - i.val))).ofIso
      (bisimplicialTotalDegreeCoproductIso R n)

theorem bisimplicialTotalDegreePresentation_generator (n : ℕ) (i : Fin (n + 1)) :
    (bisimplicialTotalDegreePresentation R n).generator i =
      (bisimplicialTotalDegreeInclusion R n i).app
        (bisimplicialRepresentable.{u} i.val (n - i.val))
          ((bisimplicialBidegreePresentation R i.val (n - i.val)).generator ()) := by
  change ((Sigma.ι (fun j : Fin (n + 1) => bisimplicialBidegreeModule R j.val (n - j.val)) i ≫
    Sigma.desc (bisimplicialTotalDegreeInclusion R n)).app
      (bisimplicialRepresentable.{u} i.val (n - i.val))) _ = _
  rw [Sigma.ι_desc]

def bisimplicialDiagonalFunctorComplex :
    ChainComplex (SimplicialObject SSet.{u} ⥤ ModuleCat.{u} R) ℕ :=
  functorChainComplex (bisimplicialDiagonalChainsFunctor R)

def bisimplicialTotalFunctorComplex :
    ChainComplex (SimplicialObject SSet.{u} ⥤ ModuleCat.{u} R) ℕ :=
  functorChainComplex (bisimplicialTotalChainsFunctor R)

def bisimplicialDiagonalFunctorComplexPresentation (n : ℕ) :
    ModelPresentation ((bisimplicialDiagonalFunctorComplex R).X n)
      (fun _ : Unit => bisimplicialRepresentable.{u} n n) :=
  bisimplicialDiagonalDegreePresentation R n

def bisimplicialTotalFunctorComplexPresentation (n : ℕ) :
    ModelPresentation ((bisimplicialTotalFunctorComplex R).X n)
      (fun i : Fin (n + 1) => bisimplicialRepresentable.{u} i.val (n - i.val)) :=
  bisimplicialTotalDegreePresentation R n

def bisimplicialAlexanderWhitneyNatTrans :
    bisimplicialDiagonalChainsFunctor R ⟶ bisimplicialTotalChainsFunctor R where
  app X := bisimplicialAlexanderWhitney X R
  naturality {_ _} φ := bisimplicialAlexanderWhitney_naturality φ R

def bisimplicialAlexanderWhitneyFunctorMap :
    bisimplicialDiagonalFunctorComplex R ⟶ bisimplicialTotalFunctorComplex R :=
  functorChainComplexMap (bisimplicialAlexanderWhitneyNatTrans R)

@[simp] theorem bisimplicialDiagonalFunctorComplex_evaluation (X : SimplicialObject SSet.{u}) :
    (((evaluation _ (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bisimplicialDiagonalFunctorComplex R) =
        bisimplicialDiagonalChains X R := rfl

@[simp] theorem bisimplicialTotalFunctorComplex_evaluation (X : SimplicialObject SSet.{u}) :
    (((evaluation _ (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bisimplicialTotalFunctorComplex R) =
        bisimplicialTotalChains X R := rfl

@[simp] theorem bisimplicialAlexanderWhitneyFunctorMap_evaluation
    (X : SimplicialObject SSet.{u}) :
    (((evaluation _ (ModuleCat.{u} R)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (bisimplicialAlexanderWhitneyFunctorMap R) =
        bisimplicialAlexanderWhitney X R := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

end Sharpness
