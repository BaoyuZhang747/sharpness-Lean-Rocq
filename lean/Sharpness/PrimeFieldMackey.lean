import Sharpness.PrimeFieldScalars
import Sharpness.ScalarMackey
import Sharpness.MackeyCategory

/-! Realizing a p-annihilated prime-local full Mackey functor over the
prime field, with a full Mackey isomorphism after scalar restriction. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness.MackeyModule
open CategoryTheory
variable (p : ℕ) [Fact p.Prime] {C : Type v} [Category.{v} C]
    {B : MackeyShape C}
    (M : MackeyModule.{u,v,w} (PrimeLocalRing.{u} p) C B)
    (killed : ∀ P (x : M.Value P), (p : PrimeLocalRing.{u} p) • x = 0)

@[reducible] def primeFieldMackeyZModValue (P : C) : Module (ZMod p) (M.Value P) :=
  AddCommGroup.zmodModule fun x => by
    rw [← Nat.cast_smul_eq_nsmul (PrimeLocalRing.{u} p)]
    exact killed P x

@[reducible] def primeFieldMackeyValue (P : C) : Module (PrimeField.{u} p) (M.Value P) := by
  letI : Module (ZMod p) (M.Value P) := primeFieldMackeyZModValue p M killed P
  exact inferInstanceAs (Module (ULift.{u} (ZMod p)) (M.Value P))

def primeFieldMackey : MackeyModule (PrimeField.{u} p) C B := by
  letI (P : C) : Module (ZMod p) (M.Value P) := primeFieldMackeyZModValue p M killed P
  letI (P : C) : Module (PrimeField.{u} p) (M.Value P) := primeFieldMackeyValue p M killed P
  exact {
  Value := M.Value
  valueAddCommGroup := M.valueAddCommGroup
  valueModule P := primeFieldMackeyValue p M killed P
  pull f :=
    { toFun := M.pull f
      map_add' := (M.pull f).map_add
      map_smul' c x := ZMod.map_smul (M.pull f).toAddMonoidHom c.down x }
  push f :=
    { toFun := M.push f
      map_add' := (M.push f).map_add
      map_smul' c x := ZMod.map_smul (M.push f).toAddMonoidHom c.down x }
  pull_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_id P) x
  push_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_id P) x
  pull_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_comp f g) x
  push_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_comp f g) x
  pull_iso f := by intro hf; apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_iso f) x
  mackey f g := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (M.mackey f g) x
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk] using h }

def primeFieldMackeyValueEquiv (P : C) :
    M.Value P ≃ₗ[PrimeLocalRing.{u} p]
      ((M.primeFieldMackey p killed).restrictScalars (PrimeLocalRing.{u} p)).Value P := by
  letI : Module (PrimeField.{u} p) (M.Value P) := primeFieldMackeyValue p M killed P
  exact {
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := (primeLocal_field_smul p r x).symm }

def primeFieldMackeyRestrictIso :
    M ≅ (M.primeFieldMackey p killed).restrictScalars (PrimeLocalRing.{u} p) :=
  isoOfLinearEquiv (M.primeFieldMackeyValueEquiv p killed)
    (fun _ _ => rfl) (fun _ _ => rfl)

end Sharpness.MackeyModule
