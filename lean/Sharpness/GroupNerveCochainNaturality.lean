import Sharpness.GroupNerveCochains

/-! The explicit nerve/inhomogeneous comparison commutes with actual
group homomorphisms and every coefficient homomorphism, before taking
cohomology. No additional reference naturality is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Simplicial Opposite
variable {R G H : Type u} [CommRing R] [Group G] [Group H]
    {A B : ModuleCat.{u} R}

theorem nerveCochainIso_coefficient (a : A ⟶ B) :
    SingularCohomology.chainDualCoefficientMap R
        ((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)) a ≫
        (nerveCochainIso R G B).hom =
      (nerveCochainIso R G A).hom ≫ coefficientCochainMap G a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

theorem nerveCochainIso_group (f : G →* H) (A : ModuleCat.{u} R) :
    SingularCohomology.chainDualMap R
        (SSet.chainComplexMap (nerveMap f.toFunctor) (ModuleCat.of R R)) A ≫
        (nerveCochainIso R G A).hom =
      (nerveCochainIso R H A).hom ≫ cochainPull (R := R) (A := A) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext g
  obtain ⟨x, rfl⟩ := (nerveTupleEquiv G n).surjective g
  change nerveCochainEquiv R G A n
      ((SSet.chainComplexMap (nerveMap f.toFunctor) (ModuleCat.of R R)).f n ≫ z)
        (nerveTuple G n x) =
    nerveCochainEquiv R H A n z (f ∘ nerveTuple G n x)
  rw [nerveCochainEquiv_apply, ← nerveTuple_map f n x, nerveCochainEquiv_apply]
  change ((nerve (SingleObj G)).ιChainComplex x ≫
      (SSet.chainComplexMap (nerveMap f.toFunctor) (ModuleCat.of R R)).f n ≫ z) (1 : R) = _
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rfl

end Sharpness.OrdinaryCohomology
