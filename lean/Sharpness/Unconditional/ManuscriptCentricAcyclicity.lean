import Sharpness.Unconditional.CentricTheoremA
import Sharpness.Unconditional.BarCalculation

/-! The centric restricted-Mackey theorem over every commutative algebra
over the actual localized integers. Restriction of scalars preserves the
Mackey identities, and the constructed bar comparison reflects acyclicity.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

namespace RestrictedMackeyModule

variable {k : Type u} [CommRing k] (R : Type u) [CommRing R] [Algebra R k]
    {C : Type u} [Category.{u} C] {B : MackeyShape C} {K : ObjectProperty C}
    (M : RestrictedMackeyModule.{u,u,u} k C B K)

local instance valueRestrict (P : K.FullSubcategory) : Module R (M.Value P) :=
  Module.restrictScalars R k _

local instance valueTower (P : K.FullSubcategory) : IsScalarTower R k (M.Value P) :=
  IsScalarTower.restrictScalars R k _

/-- Restriction of scalars preserves the actual centric-truncated Mackey law. -/
def restrictScalars : RestrictedMackeyModule.{u,u,u} R C B K where
  Value := M.Value
  valueAddCommGroup := M.valueAddCommGroup
  valueModule P := valueRestrict R M P
  pull f := (M.pull f).restrictScalars R
  push f := (M.push f).restrictScalars R
  pull_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_id P) x
  push_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_id P) x
  pull_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_comp f g) x
  push_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_comp f g) x
  pull_iso f := by intro hf; apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_iso f) x
  mackey f g := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (M.mackey f g) x
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.restrictScalars_apply] using h

/-- The coefficient is precisely the coefficient with restricted scalars. -/
def restrictScalarsCoefficientIso :
    (M.restrictScalars R).coefficient ≅
      restrictCoefficientScalars (R := R) M.coefficient :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end RestrictedMackeyModule

namespace FusionSystem

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

local instance manuscriptCentricFinite : Finite F.CentricOrbit :=
  Finite.of_injective (fun P : F.CentricOrbit => P.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance manuscriptCentricHomFinite (P Q : F.CentricOrbit) : Finite (P ⟶ Q) :=
  Finite.of_injective (fun f : P ⟶ Q => f.hom)
    (fun _ _ h => InducedCategory.hom_ext h)

include hS sat

/-- The manuscript's centric acyclicity statement for every commutative
Z_(p)-algebra, without a characteristic-zero or domain hypothesis on R. -/
theorem restrictedCentric_acyclic_of_primeLocalAlgebra
    (R : Type u) [CommRing R] [Algebra (PrimeLocalRing.{u} p) R]
    (M : RestrictedMackeyModule.{u,u,u} R F.Orbit F.mackeyShape F.centricProperty) :
    Acyclic M.coefficient := by
  let A := M.restrictScalars (PrimeLocalRing.{u} p)
  have hA : Acyclic A.coefficient := F.restrictedCentric_acyclic p hS sat A
  have hR : Acyclic (restrictCoefficientScalars (R := PrimeLocalRing.{u} p) M.coefficient) :=
    acyclic_of_iso (M.restrictScalarsCoefficientIso (PrimeLocalRing.{u} p)).symm hA
  exact (Unconditional.finiteCategoryBarScalarComparison
    (R := PrimeLocalRing.{u} p) (k := R) (C := F.CentricOrbit)).acyclic_of_restrict
      M.coefficient
      (Unconditional.finiteCategoryBarComparison (PrimeLocalRing.{u} p) F.CentricOrbit)
      (Unconditional.finiteCategoryBarComparison R F.CentricOrbit) hR

end FusionSystem
end Sharpness
