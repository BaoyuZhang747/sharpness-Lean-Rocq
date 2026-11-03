import Sharpness.Unconditional.FirstQuadrantTotalComparisonCoproduct
import Sharpness.SimplicialReplacementFunctor
import Sharpness.SimplicialReplacementLinearization

/-! Objectwise quasi-isomorphisms induce actual quasi-isomorphisms on every
column of the unnormalized simplicial replacement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    {D E : C ⥤ SSet.{u}}

theorem replacementColumnMap_inclusion (a : D ⟶ E) (i : SimplexCategory)
    (s : ComposableArrows C i.len) :
    simplicialReplacementInclusion D i s ≫ simplicialReplacementColumnMap a i =
      a.app (chainHead s) ≫ simplicialReplacementInclusion E i s := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.ext_apply
  intro x
  rfl

def replacementColumnDirectSumMap (a : D ⟶ E) (i : SimplexCategory) :
    chainReplacementColumn (simplicialChainDiagram D R) i ⟶
      chainReplacementColumn (simplicialChainDiagram E R) i :=
  coproductChainsMap
    (fun s : ComposableArrows C i.len => (simplicialChainDiagram D R).obj (chainHead s))
    (fun s : ComposableArrows C i.len => (simplicialChainDiagram E R).obj (chainHead s))
    id (fun s => (simplicialChainsFunctor R).map (a.app (chainHead s)))

/-- The existing concrete linearization is natural in the diagram. -/
theorem columnLinearization_naturality_in_diagram (a : D ⟶ E) (i : SimplexCategory) :
    replacementColumnDirectSumMap (R := R) a i ≫ (simplicialColumnLinearizationIso E R i).hom =
      (simplicialColumnLinearizationIso D R i).hom ≫
        (simplicialChainsFunctor R).map (simplicialReplacementColumnMap a i) := by
  apply coproductChains_hom_ext
  intro s
  have hm : chainReplacementInclusion (simplicialChainDiagram D R) i s ≫
        replacementColumnDirectSumMap (R := R) a i =
      (simplicialChainsFunctor R).map (a.app (chainHead s)) ≫
        chainReplacementInclusion (simplicialChainDiagram E R) i s :=
    coproductChainsMap_inclusion _ _ id _ s
  change chainReplacementInclusion (simplicialChainDiagram D R) i s ≫ _ = _
  rw [← Category.assoc, hm, Category.assoc, simplicialColumnLinearizationIso_hom,
    simplicialColumnLinearizationHom_inclusion]
  rw [← Category.assoc, simplicialColumnLinearizationIso_hom]
  have hd : coproductChainsInclusion
        (fun s : ComposableArrows C i.len => (simplicialChainDiagram D R).obj (chainHead s)) s ≫
          simplicialColumnLinearizationHom D R i =
      (simplicialChainsFunctor R).map (simplicialReplacementInclusion D i s) :=
    simplicialColumnLinearizationHom_inclusion D R i s
  rw [hd]
  exact ((simplicialChainsFunctor R).map_comp _ _).symm.trans
    ((congrArg (fun f => (simplicialChainsFunctor R).map f)
      (replacementColumnMap_inclusion a i s).symm).trans
        ((simplicialChainsFunctor R).map_comp _ _))

/-- No finiteness or projectivity assumptions on the objectwise homology maps
are needed for the replacement column comparison. -/
theorem replacementColumnChainMap_quasiIso (a : D ⟶ E)
    (ha : ∀ c, QuasiIso ((simplicialChainsFunctor R).map (a.app c))) (i : SimplexCategory) :
    QuasiIso ((simplicialChainsFunctor R).map (simplicialReplacementColumnMap a i)) := by
  letI (s : ComposableArrows C i.len) := ha (chainHead s)
  haveI : QuasiIso (replacementColumnDirectSumMap (R := R) a i) :=
    coproductChainsMap_quasiIso (fun s : ComposableArrows C i.len =>
      (simplicialChainsFunctor R).map (a.app (chainHead s)))
  haveI : QuasiIso ((simplicialColumnLinearizationIso D R i).hom ≫
      (simplicialChainsFunctor R).map (simplicialReplacementColumnMap a i)) := by
    rw [← columnLinearization_naturality_in_diagram]
    infer_instance
  exact quasiIso_of_comp_left (simplicialColumnLinearizationIso D R i).hom _

end Sharpness.TotalComparison
