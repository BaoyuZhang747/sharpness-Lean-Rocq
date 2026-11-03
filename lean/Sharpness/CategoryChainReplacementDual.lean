import Sharpness.CategoryChainReplacement
import Sharpness.CoproductChainsDual
import Sharpness.ChainDualFunctor
import Sharpness.CategoryCochainReplacement

/-! The constructed simplicial direct-sum chain replacement, after
actual Hom_R(-,A), is naturally isomorphic to the existing actual
cosimplicial product cochain replacement. The comparison is on entire
complexes and all simplex maps, not only on modules in each degree. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def chainReplacementDualIso :
    (chainReplacement D).rightOp ⋙ SingularCohomology.chainDualFunctor R A ≅
      cochainReplacement (D.op ⋙ SingularCohomology.chainDualFunctor R A) :=
  NatIso.ofComponents (fun i => coproductChainsDualIso
    (fun s : ComposableArrows C i.len => D.obj (chainHead s)) A) (by
      intro i j f
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      change (coproductChainsInclusion (fun t : ComposableArrows C j.len => D.obj (chainHead t)) s).f n ≫
        ((chainReplacementMap D f).f n ≫ x) =
        (D.map (categoryChainHeadArrow f s)).f n ≫
          ((coproductChainsInclusion (fun t : ComposableArrows C i.len => D.obj (chainHead t))
            (restrictCategoryChain f s)).f n ≫ x)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a.f n ≫ x) (chainReplacementMap_inclusion D f s)).trans
          (Category.assoc _ _ _)))

end Sharpness
