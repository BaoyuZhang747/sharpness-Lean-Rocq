import Sharpness.CentralArrow

/-! The actual quotient S/Z and its subgroups. The only fusion-structural
input is AKO II.5.5, with the defining lift relation of the quotient fusion
system. The induced group homomorphisms below are constructed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem central_fixed_element {Z P Q : Subgroup S} (hZ : F.CentralSubgroup Z)
    (f : P →* Q) (hf : F.IsHom f) (x : P) (hx : x.val ∈ Z) : (f x).val = x.val := by
  obtain ⟨g, _, hgP, hgZ⟩ := hZ.extend f hf
  exact (hgP x).symm.trans (hgZ ⟨x.val, hx⟩)

theorem central_normal {Z : Subgroup S} (hZ : F.CentralSubgroup Z) : Z.Normal := by
  constructor
  intro z hz x
  have hc := Subgroup.mem_center_iff.mp (hZ.in_center hz) x
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hz

variable (Z : Subgroup S) [Z.Normal]

abbrev quotientPreimage (_F : FusionSystem S) (Z : Subgroup S) [Z.Normal]
    (A : Subgroup (S ⧸ Z)) := A.comap (QuotientGroup.mk' Z)

def subgroupProjection (A : Subgroup (S ⧸ Z)) : F.quotientPreimage Z A →* A where
  toFun x := ⟨QuotientGroup.mk x.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupProjection_surjective (A : Subgroup (S ⧸ Z)) :
    Function.Surjective (F.subgroupProjection Z A) := by
  intro a
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z a.val
  have mem : s ∈ F.quotientPreimage Z A := by
    change QuotientGroup.mk' Z s ∈ A
    rw [hs]
    exact a.property
  exact ⟨⟨s, mem⟩, Subtype.ext hs⟩

variable {Z} (hZ : F.CentralSubgroup Z)
    {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩)

include hZ

theorem projection_kernel_le :
    (F.subgroupProjection Z A).ker ≤ ((F.subgroupProjection Z B).comp f.val).ker := by
  intro x hx
  have hq : (QuotientGroup.mk x.val : S ⧸ Z) = 1 :=
    congrArg (fun a : A => a.val) hx
  have hz := (QuotientGroup.eq_one_iff x.val).mp hq
  apply Subtype.ext
  change (QuotientGroup.mk (f.val x).val : S ⧸ Z) = 1
  rw [F.central_fixed_element hZ f.val f.property x hz]
  exact hq

def quotientInducedHom : A →* B :=
  (F.subgroupProjection Z A).liftOfSurjective (F.subgroupProjection_surjective Z A)
    ⟨(F.subgroupProjection Z B).comp f.val, F.projection_kernel_le hZ f⟩

theorem quotientInducedHom_apply (x : F.quotientPreimage Z A) :
    F.quotientInducedHom hZ f (F.subgroupProjection Z A x) =
      F.subgroupProjection Z B (f.val x) := by
  exact (F.subgroupProjection Z A).liftOfRightInverse_comp_apply
    (Function.surjInv (F.subgroupProjection_surjective Z A))
    (Function.rightInverse_surjInv (F.subgroupProjection_surjective Z A)) _ x

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (saturated : F.Saturated p)

/-- AKO II.5.5: the saturated quotient fusion system, with its defining
homomorphism-lifting rule. No orbit-category equivalence, Mackey inflation,
simple descent, or higher-limit assertion is included. -/
structure AKOQuotientInput (hZ : F.CentralSubgroup Z) (hS : IsPGroup p S)
    (saturated : F.Saturated p) where
  system : FusionSystem (S ⧸ Z)
  isHom_iff : ∀ {A B : Subgroup (S ⧸ Z)} (g : A →* B),
    system.IsHom g ↔ ∃ f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩,
      F.quotientInducedHom hZ f = g
  quotient_saturated : system.Saturated p

end Sharpness.FusionSystem
