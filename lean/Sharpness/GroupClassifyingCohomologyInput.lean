import Sharpness.SingularCohomologyEquivalence
import Sharpness.GroupCohomologyPull
import Sharpness.PrimeLocalAddHom
import Sharpness.SmallNerveMap

/-! The general classifying-space/group-cohomology calculation of AKO
III.1.7, p.113 (including its cellular free-resolution proof), at a fixed
arbitrary trivial coefficient module. Only the additive calculation and
its group-map naturality are reference inputs. Z_(p)-linearity is proved
using automatic linearity of additive maps between Z_(p)-modules.
The actual nerve realization is BG by AKO III.2.4--2.5, pp.124--125.
This is independent of fusion systems and contains no vanishing result. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory

def classifyingSpace (G : Type u) [Group G] : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve (SingleObj G))

def classifyingMap {G H : Type u} [Group G] [Group H] (f : G →* H) :
    classifyingSpace G ⟶ classifyingSpace H :=
  SSet.toTop.map (CategoryTheory.nerveMap f.toFunctor)

variable (p : ℕ) [Fact p.Prime] (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) (n : ℕ)

structure ClassifyingComparisonInput where
  AKO_III_1_7 : ∀ (G : Type u) [Group G],
    SingularCohomology.cohomology (PrimeLocalRing.{u} p) (classifyingSpace G) A n ≃+
      value (PrimeLocalRing.{u} p) G A n
  naturality : ∀ {G H : Type u} [Group G] [Group H] (f : G →* H)
      (x : SingularCohomology.cohomology (PrimeLocalRing.{u} p) (classifyingSpace H) A n),
    AKO_III_1_7 G (SingularCohomology.pull (PrimeLocalRing.{u} p) (classifyingMap f) A n x) =
      pull (R := PrimeLocalRing.{u} p) (A := A) f n (AKO_III_1_7 H x)

namespace ClassifyingComparisonInput
variable {p A n} (I : ClassifyingComparisonInput p A n)

def linearIso (G : Type u) [Group G] :
    SingularCohomology.cohomology (PrimeLocalRing.{u} p) (classifyingSpace G) A n ≅
      value (PrimeLocalRing.{u} p) G A n :=
  LinearEquiv.toModuleIso
    { toFun := I.AKO_III_1_7 G
      invFun := (I.AKO_III_1_7 G).symm
      left_inv := (I.AKO_III_1_7 G).left_inv
      right_inv := (I.AKO_III_1_7 G).right_inv
      map_add' := (I.AKO_III_1_7 G).map_add
      map_smul' := primeLocal_addHom_map_smul p (I.AKO_III_1_7 G).toAddMonoidHom }

theorem linearIso_naturality {G H : Type u} [Group G] [Group H] (f : G →* H) :
    SingularCohomology.pull (PrimeLocalRing.{u} p) (classifyingMap f) A n ≫ (I.linearIso G).hom =
      (I.linearIso H).hom ≫ pull (R := PrimeLocalRing.{u} p) (A := A) f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact I.naturality f x

end ClassifyingComparisonInput
end Sharpness.OrdinaryCohomology
