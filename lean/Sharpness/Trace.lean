import Sharpness.LinearCore

/-! The characteristic-p trace cancellation in `lem:centralizer-zero`.
The group-theoretic identification of the cosets with these finite fibres is
a separate obligation; it is not an assumption about the conclusion. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open scoped BigOperators

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

theorem repeated_trace_zero {J : Type w} {K : Type w} [Fintype J] [Fintype K]
    (f : J → V) (hcard : (Fintype.card K : R) = 0) :
    (∑ j : J, ∑ _k : K, f j) = 0 := by
  simp only [Finset.sum_const, Finset.card_univ]
  have hz (j : J) : Fintype.card K • f j = 0 := by
    rw [← Nat.cast_smul_eq_nsmul R, hcard, zero_smul]
  simp only [hz, Finset.sum_const_zero]

/-- A bijection with repeated fibres supplies precisely the multiplicity
factor in the normalizer trace, with no estimate or finite search. -/
theorem trace_zero_of_product_fibres {I J K : Type w}
    [Fintype I] [Fintype J] [Fintype K] (e : I ≃ J × K) (f : I → V)
    (g : J → V) (constant_on_fibres : ∀ i, f i = g (e i).1)
    (hcard : (Fintype.card K : R) = 0) : (∑ i, f i) = 0 := by
  calc
    (∑ i, f i) = ∑ i, g (e i).1 := Finset.sum_congr rfl (fun i _ => constant_on_fibres i)
    _ = ∑ jk : J × K, g jk.1 := e.sum_comp (fun jk => g jk.1)
    _ = ∑ j : J, ∑ _k : K, g j := Fintype.sum_prod_type (fun jk => g jk.1)
    _ = 0 := repeated_trace_zero g hcard

theorem card_cast_zero_of_prime_dvd (p : ℕ) [CharP R p] {n : ℕ} (h : p ∣ n) :
    (n : R) = 0 := by
  exact (CharP.cast_eq_zero_iff R p n).mpr h

theorem trace_zero_in_characteristic_p (p : ℕ) [CharP R p] {I J K : Type w}
    [Fintype I] [Fintype J] [Fintype K] (e : I ≃ J × K) (f : I → V)
    (g : J → V) (constant_on_fibres : ∀ i, f i = g (e i).1)
    (divides : p ∣ Fintype.card K) : (∑ i, f i) = 0 :=
  trace_zero_of_product_fibres e f g constant_on_fibres
    (card_cast_zero_of_prime_dvd (R := R) p divides)

end Sharpness
