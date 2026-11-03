import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Additivity of the native cohomology functor in its representation argument.
This gives finite-sum identities and preservation of finite biproducts for
passing actual coinduction decompositions to group cohomology. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
variable (R G : Type u) [CommRing R] [Group G]

instance nativeCohomologyFunctor_additive (n : ℕ) :
    (groupCohomology.functor R G n).Additive where
  map_add {X Y} {f g} := by
    change HomologicalComplex.homologyMap
        ((groupCohomology.cochainsFunctor R G).map (f + g)) n = _
    rw [(groupCohomology.cochainsFunctor R G).map_add]
    exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map_add

theorem nativeCohomology_map_sum (n : ℕ) {ι : Type*} (s : Finset ι)
    {X Y : Rep R G} (f : ι → (X ⟶ Y)) :
    groupCohomology.map (MonoidHom.id G) (∑ i ∈ s, f i) n =
      ∑ i ∈ s, groupCohomology.map (MonoidHom.id G) (f i) n :=
  (groupCohomology.functor R G n).map_sum f s

instance nativeCohomology_preservesFiniteBiproducts (n : ℕ) :
    PreservesFiniteBiproducts (groupCohomology.functor R G n) := inferInstance

instance nativeCohomology_preservesFiniteProducts (n : ℕ) :
    PreservesFiniteProducts (groupCohomology.functor R G n) := inferInstance

end Sharpness.OrdinaryCohomology
