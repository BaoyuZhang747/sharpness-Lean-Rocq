import Sharpness.SimplicialReplacementInclusions
import Sharpness.CategoryChainReplacement
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-! The actual chains on each replacement column are isomorphic to
the actual direct-sum chain replacement. The forward map is induced
by simplicial summand inclusions. Its inverse in each degree is
constructed on every simplex generator; no freeness comparison or
quasi-isomorphism is supplied as an assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})
    (R : Type u) [CommRing R]

abbrev simplicialChainsFunctor : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

abbrev simplicialChainDiagram : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  D ⋙ simplicialChainsFunctor R

def simplicialColumnLinearizationHom (i : SimplexCategory) :
    chainReplacementColumn (simplicialChainDiagram D R) i ⟶
      (simplicialReplacementColumn D i).chainComplex (ModuleCat.of R R) :=
  coproductChainsDesc _ (fun s =>
    SSet.chainComplexMap (simplicialReplacementInclusion D i s) (ModuleCat.of R R))

@[reassoc]
theorem simplicialColumnLinearizationHom_inclusion (i : SimplexCategory)
    (s : ComposableArrows C i.len) :
    chainReplacementInclusion (simplicialChainDiagram D R) i s ≫
        simplicialColumnLinearizationHom D R i =
      SSet.chainComplexMap (simplicialReplacementInclusion D i s) (ModuleCat.of R R) :=
  coproductChainsInclusion_desc _ _ _

theorem simplicialColumnLinearizationHom_simplex (i : SimplexCategory) (n : ℕ)
    (s : ComposableArrows C i.len) (x : (D.obj (chainHead s)).obj (op ⦋n⦌)) :
    (D.obj (chainHead s)).ιChainComplex (R := ModuleCat.of R R) x ≫
        (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n ≫
        (simplicialColumnLinearizationHom D R i).f n =
      (simplicialReplacementColumn D i).ιChainComplex ⟨s, x⟩ := by
  rw [← HomologicalComplex.comp_f, simplicialColumnLinearizationHom_inclusion]
  exact SSet.ι_chainComplexMap_f _ _ _ _ _

def simplicialColumnLinearizationInvDegree (i : SimplexCategory) (n : ℕ) :
    ((simplicialReplacementColumn D i).chainComplex (ModuleCat.of R R)).X n ⟶
      (chainReplacementColumn (simplicialChainDiagram D R) i).X n :=
  Sigma.desc (fun z => (D.obj (chainHead z.1)).ιChainComplex z.2 ≫
    (chainReplacementInclusion (simplicialChainDiagram D R) i z.1).f n)

@[reassoc]
theorem simplicialColumnLinearizationInvDegree_simplex (i : SimplexCategory) (n : ℕ)
    (s : ComposableArrows C i.len) (x : (D.obj (chainHead s)).obj (op ⦋n⦌)) :
    (simplicialReplacementColumn D i).ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        simplicialColumnLinearizationInvDegree D R i n =
      (D.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n :=
  Sigma.ι_desc _ _

def simplicialColumnLinearizationDegreeIso (i : SimplexCategory) (n : ℕ) :
    (chainReplacementColumn (simplicialChainDiagram D R) i).X n ≅
      ((simplicialReplacementColumn D i).chainComplex (ModuleCat.of R R)).X n where
  hom := (simplicialColumnLinearizationHom D R i).f n
  inv := simplicialColumnLinearizationInvDegree D R i n
  hom_inv_id := by
    apply moduleDirectSum_hom_ext
    intro s
    apply SSet.chainComplex_hom_ext
    intro x
    change (D.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n ≫
        ((simplicialColumnLinearizationHom D R i).f n ≫
          simplicialColumnLinearizationInvDegree D R i n) =
      (D.obj (chainHead s)).ιChainComplex x ≫
        (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n ≫ 𝟙 _
    calc
      _ = ((D.obj (chainHead s)).ιChainComplex x ≫
          (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n ≫
          (simplicialColumnLinearizationHom D R i).f n) ≫
          simplicialColumnLinearizationInvDegree D R i n := by simp only [Category.assoc]
      _ = (simplicialReplacementColumn D i).ιChainComplex ⟨s, x⟩ ≫
          simplicialColumnLinearizationInvDegree D R i n :=
        congrArg (fun t => t ≫ simplicialColumnLinearizationInvDegree D R i n)
          (simplicialColumnLinearizationHom_simplex D R i n s x)
      _ = (D.obj (chainHead s)).ιChainComplex x ≫
          (chainReplacementInclusion (simplicialChainDiagram D R) i s).f n :=
        simplicialColumnLinearizationInvDegree_simplex D R i n s x
      _ = _ := by simp only [Category.comp_id]
  inv_hom_id := by
    apply SSet.chainComplex_hom_ext
    rintro ⟨s, x⟩
    rw [← Category.assoc, simplicialColumnLinearizationInvDegree_simplex, Category.assoc,
      simplicialColumnLinearizationHom_simplex, Category.comp_id]

def simplicialColumnLinearizationIso (i : SimplexCategory) :
    chainReplacementColumn (simplicialChainDiagram D R) i ≅
      (simplicialReplacementColumn D i).chainComplex (ModuleCat.of R R) :=
  HomologicalComplex.Hom.isoOfComponents (simplicialColumnLinearizationDegreeIso D R i)
    (fun a b _ => (simplicialColumnLinearizationHom D R i).comm a b)

theorem simplicialColumnLinearizationIso_hom (i : SimplexCategory) :
    (simplicialColumnLinearizationIso D R i).hom = simplicialColumnLinearizationHom D R i := by
  apply HomologicalComplex.Hom.ext
  rfl

end Sharpness
