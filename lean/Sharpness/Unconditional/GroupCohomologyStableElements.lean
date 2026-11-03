import Sharpness.Unconditional.GroupCohomologyMackeyCohomology
import Sharpness.Unconditional.GroupCohomologyTransferUnit
import Sharpness.Unconditional.GroupCohomologyInner

/-! Stable elements for the actual restriction and conjugation maps on ordinary
group cohomology. The transfer computation uses the proved native Mackey law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory CategoryTheory.Preadditive
open MackeyDecomposition
open scoped BigOperators
variable {R G A : Type u} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A]

def stableElements (S : Subgroup G) (n : ℕ) : Submodule R (value R S A n) where
  carrier := {x | ∀ g : G,
    pull (intersectionConjugation S S g) n x = pull (intersection S S g).subtype n x}
  zero_mem' := by intro g; simp only [map_zero]
  add_mem' := by intro x y hx hy g; simp only [map_add, hx g, hy g]
  smul_mem' := by intro r x hx g; simp only [map_smul, hx g]

theorem restriction_mem_stableElements (S : Subgroup G) (n : ℕ)
    (x : value R G A n) : pull S.subtype n x ∈ stableElements S n := by
  intro g
  have he : S.subtype.comp (intersectionConjugation S S g) =
      ((MulAut.conj g).toMonoidHom.comp S.subtype).comp (intersection S S g).subtype := by
    ext a
    rfl
  have hc : pull (R := R) (A := A) S.subtype n ≫
      pull (intersectionConjugation S S g) n =
      pull S.subtype n ≫ pull (intersection S S g).subtype n := by
    rw [← pull_comp, he, pull_comp, pull_comp, pull_inner, Category.id_comp]
  exact congrArg (fun f => f.hom x) hc

def restrictionToStableElements (S : Subgroup G) (n : ℕ) :
    value R G A n →ₗ[R] stableElements (R := R) (A := A) S n :=
  (pull S.subtype n).hom.codRestrict _ (restriction_mem_stableElements S n)

variable [Finite G]

local instance stableDoubleCosetFintype (H K : Subgroup G) :
    Fintype (DoubleCoset.Quotient (H : Set G) K) := by
  unfold DoubleCoset.Quotient
  exact Fintype.ofFinite _

theorem sum_intersection_indices (H K : Subgroup G) :
    (∑ d : DoubleCoset.Quotient (H : Set G) K, (intersection H K d.out).index) =
      H.index := by
  have h := Nat.card_congr (rightCosetDoubleEquiv H K)
  rw [Nat.card_sigma] at h
  have hr (J : Subgroup K) : Nat.card (Quotient (QuotientGroup.rightRel J)) = J.index :=
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel J)
  have hl : Nat.card (Quotient (QuotientGroup.rightRel H)) = H.index :=
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  simpa only [hr, hl] using h

theorem transfer_restrict_stable (S : Subgroup G) (n : ℕ)
    (x : stableElements (R := R) (A := A) S n) :
    pull S.subtype n (transfer S n x.1) = S.index • x.1 := by
  have h := congrArg (fun f => f.hom x.1)
    (transfer_pull_doubleCoset (R := R) (A := A) S S n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum, LinearMap.sum_apply] at h
  rw [h]
  calc
    _ = ∑ d : DoubleCoset.Quotient (S : Set G) S,
        (intersection S S d.out).index • x.1 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [x.2 d.out]
      exact congrArg (fun f => f.hom x.1)
        (pull_transfer (R := R) (A := A) (intersection S S d.out) n)
    _ = (∑ d : DoubleCoset.Quotient (S : Set G) S,
        (intersection S S d.out).index) • x.1 := Finset.sum_smul.symm
    _ = S.index • x.1 := by rw [sum_intersection_indices]

end Sharpness.OrdinaryCohomology
