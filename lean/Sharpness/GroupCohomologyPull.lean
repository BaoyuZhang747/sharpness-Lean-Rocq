import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Ordinary group cohomology and its actual pullbacks on trivial
coefficients. Values and arrows are Mathlib's native cohomology objects
and homology maps of the explicit inhomogeneous cochain complex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G H K A : Type u} [CommRing R] [Group G] [Group H] [Group K]
    [AddCommGroup A] [Module R A]

abbrev value (R G A : Type u) [CommRing R] [Group G] [AddCommGroup A] [Module R A]
    (n : ℕ) : ModuleCat.{u} R := groupCohomology (Rep.trivial R G A) n

def trivialRestrictionHom (f : G →* H) :
    Rep.res f (Rep.trivial R H A) ⟶ Rep.trivial R G A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def cochainPull (f : G →* H) :
    groupCohomology.inhomogeneousCochains (Rep.trivial R H A) ⟶
      groupCohomology.inhomogeneousCochains (Rep.trivial R G A) :=
  groupCohomology.cochainsMap f (trivialRestrictionHom f)

theorem cochainPull_id : cochainPull (R := R) (A := A) (MonoidHom.id G) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem cochainPull_comp (f : G →* H) (g : H →* K) :
    cochainPull (R := R) (A := A) (g.comp f) = cochainPull g ≫ cochainPull f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def pull (f : G →* H) (n : ℕ) : value R H A n ⟶ value R G A n :=
  HomologicalComplex.homologyMap (cochainPull f) n

theorem pull_id (n : ℕ) : pull (R := R) (A := A) (MonoidHom.id G) n = 𝟙 _ := by
  rw [pull, cochainPull_id, HomologicalComplex.homologyMap_id]
  rfl

theorem pull_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    pull (R := R) (A := A) (g.comp f) n = pull g n ≫ pull f n := by
  rw [pull, cochainPull_comp, HomologicalComplex.homologyMap_comp]
  rfl

def pullLinear (f : G →* H) (n : ℕ) : value R H A n →ₗ[R] value R G A n :=
  (pull f n).hom

theorem pullLinear_id (n : ℕ) :
    pullLinear (R := R) (A := A) (MonoidHom.id G) n = LinearMap.id :=
  congrArg (fun f : value R G A n ⟶ value R G A n => f.hom) (pull_id n)

theorem pullLinear_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    pullLinear (R := R) (A := A) (g.comp f) n =
      (pullLinear f n).comp (pullLinear g n) :=
  congrArg (fun t : value R K A n ⟶ value R G A n => t.hom) (pull_comp f g n)

end Sharpness.OrdinaryCohomology
