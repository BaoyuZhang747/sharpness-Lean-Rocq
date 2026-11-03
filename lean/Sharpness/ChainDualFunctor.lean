import Sharpness.SingularCochains

/-! The actual Hom_R(-,A) chain dual is a contravariant functor on
chain complexes, with arbitrary constant coefficient module A. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory Opposite
variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem chainDualMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    chainDualMap R (𝟙 K) A = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (𝟙 (K.X n)) ≫ a = a
  exact Category.id_comp _

theorem chainDualMap_comp {K L M : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    chainDualMap R (f ≫ g) A = chainDualMap R g A ≫ chainDualMap R f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (f.f n ≫ g.f n) ≫ a = f.f n ≫ (g.f n ≫ a)
  exact Category.assoc _ _ _

def chainDualFunctor : (ChainComplex (ModuleCat.{u} R) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj K := K.unop.linearYonedaObj R A
  map f := chainDualMap R f.unop A
  map_id K := chainDualMap_id R A K.unop
  map_comp f g := chainDualMap_comp R A g.unop f.unop

end Sharpness.SingularCohomology
