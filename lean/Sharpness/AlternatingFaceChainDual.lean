import Sharpness.ChainDualFiniteSums
import Sharpness.DualNatBicomplex
import Sharpness.AlternatingCofaceFunctorIso

/-! Dualizing the actual alternating face chain complex gives the
actual alternating coface complex. The horizontal signs and all
vertical differentials are retained. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R : Type u} [CommRing R]
    (X : SimplicialObject (ChainComplex (ModuleCat.{u} R) ℕ)) (A : ModuleCat.{u} R)

theorem alternatingFaceChain_d (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).obj X).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • X.δ i :=
  ChainComplex.of_d (fun n => X.obj (op ⦋n⦌)) (AlgebraicTopology.AlternatingFaceMapComplex.objD X) n

set_option backward.isDefEq.respectTransparency false in
def alternatingFaceChainDualIso :
    dualNatBicomplex
        ((AlgebraicTopology.alternatingFaceMapComplex (ChainComplex (ModuleCat.{u} R) ℕ)).obj X) A ≅
      (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).obj
        (X.rightOp ⋙ SingularCohomology.chainDualFunctor R A) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have hj : i+1=j := hij
    subst j
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, dualNatBicomplex_horizontal,
      alternatingFaceChain_d, alternatingCoface_d, SingularCohomology.chainDualMap_sum,
      SingularCohomology.chainDualMap_zsmul]
    rfl)

end Sharpness
