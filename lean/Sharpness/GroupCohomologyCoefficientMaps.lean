import Sharpness.GroupCohomologyPull

/-! Coefficient homomorphisms on the actual inhomogeneous cochain
complex. Their compatibility with group pullback is proved before
passing to native cohomology. No comparison theorem is assumed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R : Type u} [CommRing R] {G H : Type u} [Group G] [Group H]
    {A B C : ModuleCat.{u} R}

def coefficientCochainMap (G : Type u) [Group G] (a : A ⟶ B) :
    groupCohomology.inhomogeneousCochains (Rep.trivial R G A) ⟶
      groupCohomology.inhomogeneousCochains (Rep.trivial R G B) :=
  groupCohomology.cochainsMap (MonoidHom.id G) ((Rep.trivialFunctor R G).map a)

theorem coefficientCochainMap_apply (a : A ⟶ B) (n : ℕ)
    (x : (Fin n → G) → A) (g : Fin n → G) :
    (coefficientCochainMap G a).f n x g = a (x g) := rfl

theorem coefficientCochainMap_id : coefficientCochainMap G (𝟙 A) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem coefficientCochainMap_comp (a : A ⟶ B) (b : B ⟶ C) :
    coefficientCochainMap G (a ≫ b) =
      coefficientCochainMap G a ≫ coefficientCochainMap G b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem cochainPull_coefficient_naturality (f : G →* H) (a : A ⟶ B) :
    coefficientCochainMap H a ≫ cochainPull (R := R) (A := B) f =
      cochainPull (R := R) (A := A) f ≫ coefficientCochainMap G a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def coefficientMap (G : Type u) [Group G] (a : A ⟶ B) (n : ℕ) :
    value R G A n ⟶ value R G B n :=
  HomologicalComplex.homologyMap (coefficientCochainMap G a) n

theorem coefficientMap_id (n : ℕ) : coefficientMap G (𝟙 A) n = 𝟙 _ := by
  rw [coefficientMap, coefficientCochainMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem coefficientMap_comp (a : A ⟶ B) (b : B ⟶ C) (n : ℕ) :
    coefficientMap G (a ≫ b) n = coefficientMap G a n ≫ coefficientMap G b n := by
  rw [coefficientMap, coefficientCochainMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem pull_coefficient_naturality (f : G →* H) (a : A ⟶ B) (n : ℕ) :
    coefficientMap H a n ≫ pull (R := R) (A := B) f n =
      pull (R := R) (A := A) f n ≫ coefficientMap G a n := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun t => HomologicalComplex.homologyMap t n)
      (cochainPull_coefficient_naturality f a)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

end Sharpness.OrdinaryCohomology
