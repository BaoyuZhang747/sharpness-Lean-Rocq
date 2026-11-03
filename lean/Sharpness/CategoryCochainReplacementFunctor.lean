import Sharpness.CategoryCochainReplacement

/-! The actual double cochain and total complex constructions are
functorial in the whole coefficient diagram. This will supply coefficient
naturality, without postulating naturality of an edge isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    {D E : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ}

def cochainReplacementNatTrans (a : D ⟶ E) : cochainReplacement D ⟶ cochainReplacement E where
  app i := productCochainsMap _ _ id (fun s => a.app (op (chainHead s)))
  naturality {i j} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    exact congrArg (fun t => t.f n (x (restrictCategoryChain f s)))
      (a.naturality (categoryChainHeadArrow f s).op)

def cochainReplacementFunctor :
    (Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ) ⥤
      CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ) where
  obj := cochainReplacement
  map := cochainReplacementNatTrans
  map_id D := by
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp a b := by
    apply NatTrans.ext
    funext i
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def cochainReplacementBicomplexFunctor :
    (Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ) ⥤
      HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  cochainReplacementFunctor ⋙
    AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementTotalFunctor :
    (Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ) ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainReplacementBicomplexFunctor ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)

theorem cochainReplacementNatTrans_component (a : D ⟶ E) (i n : ℕ)
    (x : (cochainReplacementColumn D ⦋i⦌).X n) (s : ComposableArrows C i) :
    ((cochainReplacementNatTrans a).app ⦋i⦌).f n x s = (a.app (op (chainHead s))).f n (x s) := rfl

end Sharpness
