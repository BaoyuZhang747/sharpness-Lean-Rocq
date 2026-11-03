import Sharpness.ChainDualFunctor

/-! Actual chain duality preserves sums, zero, and scalar multiples of
chain maps. These identities control alternating face maps and signs. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}

theorem chainDualMap_zero : chainDualMap R (0 : K ⟶ L) A = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (0 : K.X n ⟶ L.X n) ≫ z = 0
  exact zero_comp

theorem chainDualMap_add (f g : K ⟶ L) :
    chainDualMap R (f+g) A = chainDualMap R f A + chainDualMap R g A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (f.f n + g.f n) ≫ z = f.f n ≫ z + g.f n ≫ z
  simp only [Preadditive.add_comp]

theorem chainDualMap_smul (r : R) (f : K ⟶ L) :
    chainDualMap R (r • f) A = r • chainDualMap R f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (r • f.f n) ≫ z = r • (f.f n ≫ z)
  simp only [Linear.smul_comp]

instance chainDualFunctor_additive : (chainDualFunctor R A).Additive where
  map_add := by
    intro X Y f g
    exact chainDualMap_add R A f.unop g.unop

end Sharpness.SingularCohomology
