import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Right-coset representatives in a subgroup tower. The inverse map sends
the pair of classes represented by g and q to the class represented by qg,
which is the order required by the coinduction trace formula. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open QuotientGroup
open scoped BigOperators

variable {G : Type u} [Group G] {P Q : Subgroup G}

/-- Right-coset factorization for nested subgroups, with explicit multiplication
order. No finiteness or normality assumption is needed. -/
def rightCosetTowerEquiv (hPQ : P ≤ Q) :
    Quotient (rightRel P) ≃ Quotient (rightRel Q) × Quotient (rightRel (P.subgroupOf Q)) where
  toFun a :=
    ⟨a.map' id (fun _ _ h => rightRel_apply.mpr (hPQ (rightRel_apply.mp h))),
      a.map' (fun g : G =>
        (⟨g * (Quotient.out (Quotient.mk'' g : Quotient (rightRel Q)))⁻¹,
          rightRel_apply.mp (Quotient.exact'
            (Quotient.out_eq' (Quotient.mk'' g : Quotient (rightRel Q))))⟩ : Q))
        (fun b c h => by
          rw [rightRel_apply]
          change (c * (Quotient.out (Quotient.mk'' c : Quotient (rightRel Q)))⁻¹) *
            (b * (Quotient.out (Quotient.mk'' b : Quotient (rightRel Q)))⁻¹)⁻¹ ∈ P
          have key : (Quotient.mk'' b : Quotient (rightRel Q)) = Quotient.mk'' c :=
            Quotient.sound' (rightRel_apply.mpr (hPQ (rightRel_apply.mp h)))
          rw [key]
          simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
            using rightRel_apply.mp h)⟩
  invFun a := a.2.map' (fun b : Q => (b : G) * a.1.out) (fun b c h => by
    rw [rightRel_apply] at h ⊢
    change (c : G) * (b : G)⁻¹ ∈ P at h
    change ((c : G) * a.1.out) * ((b : G) * a.1.out)⁻¹ ∈ P
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h)
  left_inv := by
    refine Quotient.ind' fun a => ?_
    simp only [Quotient.map'_mk'', id_eq, inv_mul_cancel_right]
  right_inv := by
    refine Prod.rec fun a b => ?_
    refine Quotient.inductionOn' b fun b => ?_
    have key : (Quotient.mk'' ((b : G) * a.out) : Quotient (rightRel Q)) = a := by
      have he : (Quotient.mk'' a.out : Quotient (rightRel Q)) =
          Quotient.mk'' ((b : G) * a.out) :=
        Quotient.sound' (rightRel_apply.mpr (show
          ((b : G) * a.out) * a.out⁻¹ ∈ Q by
            simpa only [mul_inv_cancel_right] using b.property))
      exact he.symm.trans (Quotient.out_eq' a)
    simp only [Quotient.map'_mk'', id_eq, key, mul_inv_cancel_right]

/-- The chosen tower representative has the expected right coset. -/
theorem rightCosetTowerEquiv_symm_mk (hPQ : P ≤ Q)
    (a : Quotient (rightRel Q)) (b : Q) :
    (rightCosetTowerEquiv hPQ).symm (a, Quotient.mk'' b) =
      (Quotient.mk'' ((b : G) * a.out) : Quotient (rightRel P)) := rfl

/-- The inverse equivalence uses the chosen representative of the inner class. -/
theorem rightCosetTowerEquiv_symm_apply (hPQ : P ≤ Q)
    (a : Quotient (rightRel Q)) (b : Quotient (rightRel (P.subgroupOf Q))) :
    (rightCosetTowerEquiv hPQ).symm (a, b) =
      (Quotient.mk'' ((b.out : G) * a.out) : Quotient (rightRel P)) := by
  conv_lhs => rw [← Quotient.out_eq' b]
  rfl

/-- A left-P-invariant function has the same value on equal right cosets. -/
theorem rightCosetInvariant_eq {B : Type*} (f : G → B)
    (hf : ∀ (p : P) (g : G), f ((p : G) * g) = f g)
    {a b : G} (hab : (Quotient.mk'' a : Quotient (rightRel P)) = Quotient.mk'' b) :
    f a = f b := by
  have hp : b * a⁻¹ ∈ P := rightRel_apply.mp (Quotient.exact' hab)
  have h := hf ⟨b * a⁻¹, hp⟩ a
  simpa only [Subtype.coe_mk, inv_mul_cancel_right] using h.symm

/-- A sum over right cosets decomposes into the two sums of a subgroup tower.
The statement is independent of the choices of representatives. -/
theorem rightCosetTower_sum (hPQ : P ≤ Q) {B : Type*} [AddCommMonoid B]
    [Fintype (Quotient (rightRel P))] [Fintype (Quotient (rightRel Q))]
    [Fintype (Quotient (rightRel (P.subgroupOf Q)))]
    (f : G → B) (hf : ∀ (p : P) (g : G), f ((p : G) * g) = f g) :
    (∑ a : Quotient (rightRel P), f a.out) =
      ∑ a : Quotient (rightRel Q),
        ∑ b : Quotient (rightRel (P.subgroupOf Q)), f ((b.out : G) * a.out) := by
  classical
  rw [← (rightCosetTowerEquiv hPQ).symm.sum_comp (fun a => f a.out),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply rightCosetInvariant_eq f hf
  exact (Quotient.out_eq' ((rightCosetTowerEquiv hPQ).symm (a, b))).trans
    (rightCosetTowerEquiv_symm_apply hPQ a b)

end Sharpness.OrdinaryCohomology
