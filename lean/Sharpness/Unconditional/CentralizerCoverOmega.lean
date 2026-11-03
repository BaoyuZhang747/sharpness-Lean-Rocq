import Sharpness.Unconditional.CentralizerCover
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The canonical central elementary subgroup and the section of the
centralizer cover. The adjunction uses actual orbit morphisms throughout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness
open CategoryTheory

variable {S : Type u} [Group S]

/-- The subgroup Ω₁Z(P), expressed as an ambient subgroup. -/
def centralOmega (p : ℕ) (P : Subgroup S) : Subgroup S where
  carrier := {x | x ∈ P ⊓ Subgroup.centralizer (P : Set S) ∧ x ^ p = 1}
  one_mem' := ⟨(P ⊓ Subgroup.centralizer (P : Set S)).one_mem, one_pow p⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨(P ⊓ Subgroup.centralizer (P : Set S)).mul_mem hx.1 hy.1, ?_⟩
    have hc : Commute x y :=
      ((Subgroup.mem_centralizer_iff.mp hx.1.2) y hy.1.1).symm
    rw [hc.mul_pow, hx.2, hy.2, one_mul]
  inv_mem' := by
    intro x hx
    refine ⟨(P ⊓ Subgroup.centralizer (P : Set S)).inv_mem hx.1, ?_⟩
    rw [inv_pow, hx.2, inv_one]

theorem mem_centralOmega_iff (p : ℕ) (P : Subgroup S) (x : S) :
    x ∈ centralOmega p P ↔
      (x ∈ P ∧ x ∈ Subgroup.centralizer (P : Set S)) ∧ x ^ p = 1 := Iff.rfl

namespace FusionSystem
variable (F : FusionSystem S) (p : ℕ)

theorem centralOmega_ne_bot [Finite S] [Fact p.Prime] [Nontrivial S]
    (hS : IsPGroup p S) {P : Subgroup S} (hP : F.IsCentric P) :
    centralOmega p P ≠ ⊥ := by
  letI : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hpdiv : p ∣ Nat.card (Subgroup.center S) :=
    ((hS.to_subgroup (Subgroup.center S)).card_eq_or_dvd).resolve_left
      (ne_of_gt Finite.one_lt_card)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) p hpdiv
  have hz_ne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact (Fact.out : p.Prime).ne_one hz.symm
  have hzC : z.val ∈ Subgroup.centralizer (P : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x _
    exact (Subgroup.mem_center_iff.mp z.property) x
  have hzP : z.val ∈ P :=
    hP P le_top (MulEquiv.refl P) (F.id_mem P) ⟨hzC, Subgroup.mem_top _⟩
  have hzpow : z.val ^ p = 1 := by
    have hh := pow_orderOf_eq_one z
    rw [hz] at hh
    exact congrArg Subtype.val hh
  have hzΩ : z.val ∈ centralOmega p P := ⟨⟨hzP, hzC⟩, hzpow⟩
  intro hbot
  have hz1 : z.val = 1 := Subgroup.mem_bot.mp (hbot ▸ hzΩ)
  exact hz_ne (Subtype.ext hz1)

/-- Every exponent-p central element of a target lifts to Ω₁Z(P) along a
fusion morphism whose source P is centric. -/
theorem centralOmega_lift {P Q : F.Object} (hP : F.IsCentric P.subgroup)
    (f : P ⟶ Q) (z : S)
    (hzC : z ∈ Subgroup.centralizer (Q.subgroup : Set S)) (hzpow : z ^ p = 1) :
    ∃ a : centralOmega p P.subgroup,
      (f.val ⟨a.val, a.property.1.1⟩).val = z := by
  let D := F.imageSubgroup f
  let e : P.subgroup ≃* D := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective f.val f.property))
  have he : F.IsHom e.toMonoidHom := (F.toImage f).property
  have hzD : z ∈ D := by
    apply hP D le_top e he
    refine ⟨?_, Subgroup.mem_top _⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hzC) x (F.image_le f hx)
  obtain ⟨a, ha⟩ := hzD
  have hfa : (f.val a).val = z := ha
  have haC : a.val ∈ Subgroup.centralizer (P.subgroup : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hc : (⟨x, hx⟩ : P.subgroup) * a = a * ⟨x, hx⟩ := by
      apply F.injective f.val f.property
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul, hfa]
      exact (Subgroup.mem_centralizer_iff.mp hzC) _ (f.val ⟨x, hx⟩).property
    exact congrArg Subtype.val hc
  have hapow : a.val ^ p = 1 := by
    have hapow' : a ^ p = 1 := by
      apply F.injective f.val f.property
      apply Subtype.ext
      simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, hfa] using hzpow
    exact congrArg Subtype.val hapow'
  exact ⟨⟨a.val, ⟨a.property, haC⟩, hapow⟩, hfa⟩

variable [Finite S] [Fact p.Prime] [Nontrivial S] (hS : IsPGroup p S)

def centralizerCoverSectionObj (P : F.CentricOrbit) : F.CentralizerCover p where
  centric := P
  elementary := centralOmega p P.obj.as.subgroup
  nontrivial := F.centralOmega_ne_bot p hS P.property
  le_subgroup _ h := h.1.1
  centralizes _ h := h.1.2
  exponent _ h := h.2

/-- Every underlying orbit arrow lifts uniquely from the canonical section. -/
def centralizerCoverLift (P : F.CentricOrbit) (B : F.CentralizerCover p)
    (f : P ⟶ B.centric) : F.centralizerCoverSectionObj p hS P ⟶ B := by
  refine ⟨f, ?_⟩
  obtain ⟨g, hg⟩ := F.toOrbit.map_surjective f.hom
  refine ⟨g, hg, ?_⟩
  intro b
  exact F.centralOmega_lift p P.property g b.val
    (B.centralizes b.property) (B.exponent b.val b.property)

def centralizerCoverSection : F.CentricOrbit ⥤ F.CentralizerCover p where
  obj := F.centralizerCoverSectionObj p hS
  map {P Q} f := F.centralizerCoverLift p hS P (F.centralizerCoverSectionObj p hS Q) f
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

def centralizerCoverSectionAdjunction :
    F.centralizerCoverSection p hS ⊣ F.centralizerCoverForget p :=
  Adjunction.mkOfHomEquiv
    { homEquiv P B :=
        { toFun f := f.val
          invFun f := F.centralizerCoverLift p hS P B f
          left_inv _ := Subtype.ext rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm := fun _ _ => Subtype.ext rfl
      homEquiv_naturality_right := fun _ _ => rfl }

end FusionSystem
end Sharpness
