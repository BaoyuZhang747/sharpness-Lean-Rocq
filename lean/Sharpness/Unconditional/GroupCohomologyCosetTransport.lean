import Sharpness.Unconditional.GroupCohomologyCosetTower
import Mathlib.GroupTheory.Index

/-! Transport of right-coset sums along actual group isomorphisms, and the
subgroup tower formula with all subgroup types referring to one ambient group. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open QuotientGroup
open scoped BigOperators

/-- Transport right cosets along a group isomorphism carrying one subgroup to another. -/
def rightCosetEquivOfMulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup G) (Q : Subgroup H)
    (h : ∀ g : G, g ∈ P ↔ e g ∈ Q) :
    Quotient (rightRel P) ≃ Quotient (rightRel Q) :=
  Quotient.congr e.toEquiv (fun a b => by
    rw [rightRel_apply, rightRel_apply]
    change b * a⁻¹ ∈ P ↔ e b * (e a)⁻¹ ∈ Q
    simpa only [map_mul, map_inv] using h (b * a⁻¹))

/-- Sum transport does not depend on choices of quotient representatives. -/
theorem rightCoset_sum_equiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (P : Subgroup G) (Q : Subgroup H)
    (h : ∀ g : G, g ∈ P ↔ e g ∈ Q)
    [Fintype (Quotient (rightRel P))] [Fintype (Quotient (rightRel Q))]
    {B : Type*} [AddCommMonoid B] (f : H → B)
    (hf : ∀ (q : Q) (g : H), f ((q : H) * g) = f g) :
    (∑ a : Quotient (rightRel P), f (e a.out)) =
      ∑ b : Quotient (rightRel Q), f b.out := by
  classical
  let E := rightCosetEquivOfMulEquiv e P Q h
  calc
    _ = ∑ a : Quotient (rightRel P), f (E a).out := by
      apply Finset.sum_congr rfl
      intro a _
      apply rightCosetInvariant_eq f hf
      have he : (Quotient.mk'' (e a.out) : Quotient (rightRel Q)) = E a := by
        change E (Quotient.mk'' a.out) = E a
        rw [Quotient.out_eq']
      exact he.trans (Quotient.out_eq' (E a)).symm
    _ = _ := E.sum_comp (fun a => f a.out)

variable {G : Type u} [Group G]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The two-step coset sum with P, Q and T all literal subgroups of G. -/
theorem subgroupRightCosetTower_sum (P Q T : Subgroup G) (hPQ : P ≤ Q) (hQT : Q ≤ T)
    [(P.subgroupOf T).FiniteIndex] [(Q.subgroupOf T).FiniteIndex]
    [(P.subgroupOf Q).FiniteIndex]
    {B : Type*} [AddCommMonoid B] (f : T → B)
    (hf : ∀ (p : P.subgroupOf T) (t : T), f ((p : T) * t) = f t) :
    (∑ a : Quotient (rightRel (P.subgroupOf T)), f a.out) =
      ∑ a : Quotient (rightRel (Q.subgroupOf T)),
        ∑ b : Quotient (rightRel (P.subgroupOf Q)),
          f ((⟨(b.out : G), hQT b.out.property⟩ : T) * a.out) := by
  classical
  have hPTQT : P.subgroupOf T ≤ Q.subgroupOf T := fun x hx => hPQ hx
  rw [rightCosetTower_sum hPTQT f hf]
  apply Finset.sum_congr rfl
  intro a _
  let e := Subgroup.subgroupOfEquivOfLe hQT
  let g : Q → B := fun q => f ((e.symm q : T) * a.out)
  have hg : ∀ (p : P.subgroupOf Q) (q : Q), g ((p : Q) * q) = g q := by
    intro p q
    have hp : (e.symm (p : Q) : T) ∈ P.subgroupOf T := p.property
    have he : (e.symm ((p : Q) * q) : T) = (e.symm (p : Q) : T) * (e.symm q : T) :=
      congrArg (fun z : Q.subgroupOf T => (z : T)) (e.symm.map_mul _ _)
    change f ((e.symm ((p : Q) * q) : T) * a.out) =
      f ((e.symm q : T) * a.out)
    rw [he, mul_assoc]
    exact hf ⟨_, hp⟩ _
  have hm : ∀ x : Q.subgroupOf T,
      x ∈ (P.subgroupOf T).subgroupOf (Q.subgroupOf T) ↔ e x ∈ P.subgroupOf Q :=
    fun _ => Iff.rfl
  have hs := rightCoset_sum_equiv e
    ((P.subgroupOf T).subgroupOf (Q.subgroupOf T)) (P.subgroupOf Q) hm g hg
  calc
    _ = ∑ b : Quotient (rightRel (P.subgroupOf Q)), g b.out := by
      simpa only [g, MulEquiv.symm_apply_apply] using hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      change f ((e.symm b.out : T) * a.out) =
        f ((⟨(b.out : G), hQT b.out.property⟩ : T) * a.out)
      apply congrArg (fun t : T => f (t * a.out))
      apply Subtype.ext
      rfl

end Sharpness.OrdinaryCohomology
