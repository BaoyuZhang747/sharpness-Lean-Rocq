import Sharpness.PrimeLocalRing
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The algebraic unit-detection step for the centric Burnside-ring argument.

For a finite free commutative algebra over a domain, a square family of
algebra-valued marks with nonzero determinant detects units. The determinant
need not be a unit. This is the feature needed for integral tables of marks:
their diagonal entries may be divisible by the coefficient characteristic.

This file does not assume or assert Mackey acyclicity. Construction of the
slice Burnside algebras and their action on higher limits is separate work.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.Burnside

open scoped BigOperators

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    {ι : Type w} [Fintype ι] [DecidableEq ι]

instance intPrimeLocal_isDomain (p : ℕ) [Fact p.Prime] : IsDomain (IntPrimeLocal p) :=
  IsLocalization.isDomain_of_atPrime (IntPrimeLocal p) (characteristicPrime p)

instance intPrimeLocal_charZero (p : ℕ) [Fact p.Prime] : CharZero (IntPrimeLocal p) :=
  charZero_of_injective_algebraMap (R := ℤ)
    (IsLocalization.injective (IntPrimeLocal p)
      (characteristicPrime p).primeCompl_le_nonZeroDivisors)

instance primeLocalRing_isDomain (p : ℕ) [Fact p.Prime] : IsDomain (PrimeLocalRing.{u} p) :=
  MulEquiv.isDomain (IntPrimeLocal p) ULift.ringEquiv.toMulEquiv

instance primeLocalRing_charZero (p : ℕ) [Fact p.Prime] : CharZero (PrimeLocalRing.{u} p) :=
  RingHom.charZero (ULift.ringEquiv : PrimeLocalRing.{u} p ≃+* IntPrimeLocal p).toRingHom

/-- The table of a family of marks on a chosen additive basis. -/
def markMatrix (b : Module.Basis ι R A) (mark : ι → A →ₐ[R] R) : Matrix ι ι R :=
  fun i j => mark i (b j)

/-- Marks intertwine multiplication with the diagonal matrix of mark values. -/
theorem markMatrix_mul_leftMulMatrix
    (b : Module.Basis ι R A) (mark : ι → A →ₐ[R] R) (a : A) :
    markMatrix b mark * Algebra.leftMulMatrix b a =
      Matrix.diagonal (fun i => mark i a) * markMatrix b mark := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul, markMatrix]
  have h := congrArg (fun x => mark i x) (b.sum_repr (a * b j))
  simp only [map_sum, map_smul, smul_eq_mul, map_mul] at h
  simpa only [mul_comm] using h

/-- The determinant of multiplication is the product of all marks, even when
the mark matrix is not invertible over the coefficient ring. -/
theorem det_leftMulMatrix_eq_prod_marks [IsDomain R]
    (b : Module.Basis ι R A) (mark : ι → A →ₐ[R] R)
    (hmark : (markMatrix b mark).det ≠ 0) (a : A) :
    (Algebra.leftMulMatrix b a).det = ∏ i, mark i a := by
  have h := congrArg Matrix.det (markMatrix_mul_leftMulMatrix b mark a)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  apply mul_left_cancel₀ hmark
  simpa only [mul_comm] using h

/-- A multiplication matrix with unit determinant supplies an inverse of the
original algebra element. No domain hypothesis on the algebra is needed. -/
theorem isUnit_of_isUnit_det_leftMulMatrix (b : Module.Basis ι R A) (a : A)
    (hdet : IsUnit (Algebra.leftMulMatrix b a).det) : IsUnit a := by
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  obtain ⟨v, hv⟩ := hs (b.repr 1)
  refine isUnit_iff_exists_inv.mpr ⟨b.equivFun.symm v, ?_⟩
  have he := Algebra.leftMulMatrix_mulVec_repr b a (b.equivFun.symm v)
  have hev : (b.repr (b.equivFun.symm v) : ι → R) = v := by
    simpa only [b.equivFun_apply] using b.equivFun.apply_symm_apply v
  rw [hev] at he
  exact b.ext_elem fun i => congrFun (he.symm.trans hv) i

/-- A nondegenerate square table of marks detects units over any domain. -/
theorem isUnit_of_marks [IsDomain R]
    (b : Module.Basis ι R A) (mark : ι → A →ₐ[R] R)
    (hmark : (markMatrix b mark).det ≠ 0) (a : A)
    (ha : ∀ i, IsUnit (mark i a)) : IsUnit a := by
  apply isUnit_of_isUnit_det_leftMulMatrix b a
  rw [det_leftMulMatrix_eq_prod_marks b mark hmark]
  exact IsUnit.prod_univ_iff.mpr ha

/-- The converse follows by functoriality, giving an exact criterion. -/
theorem isUnit_iff_marks [IsDomain R]
    (b : Module.Basis ι R A) (mark : ι → A →ₐ[R] R)
    (hmark : (markMatrix b mark).det ≠ 0) (a : A) :
    IsUnit a ↔ ∀ i, IsUnit (mark i a) := by
  constructor
  · intro ha i
    exact ha.map (mark i)
  · exact isUnit_of_marks b mark hmark a

/-- A ranked matrix is nonsingular when equal-rank blocks are diagonal and
all diagonal entries are nonzero. No ordering of the chosen representatives
is needed. -/
theorem det_ne_zero_of_rank [IsDomain R] (M : Matrix ι ι R) (rank : ι → ℕ)
    (hsmall : ∀ i j, rank j < rank i → M i j = 0)
    (hequal : ∀ i j, rank i = rank j → i ≠ j → M i j = 0)
    (hdiag : ∀ i, M i i ≠ 0) : M.det ≠ 0 := by
  classical
  have htri : M.BlockTriangular rank := fun {i j} h => hsmall i j h
  rw [htri.det]
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  have hblock : M.toSquareBlock rank r =
      Matrix.diagonal (fun i : {i // rank i = r} => M i.val i.val) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.toSquareBlock_def]
    · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp only [Matrix.diagonal_apply_ne _ hij]
      exact hequal i.val j.val (i.property.trans j.property.symm) hij'
  rw [hblock, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i.val

/-- Prime-to-p integers are units in the actual localization used by the
restricted Mackey theorem. -/
theorem isUnit_natCast_intPrimeLocal (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hn : ¬ p ∣ n) : IsUnit (n : IntPrimeLocal p) := by
  have hm : (n : ℤ) ∈ (characteristicPrime p).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    rw [characteristicPrime_eq_span, Ideal.mem_span_singleton]
    exact_mod_cast hn
  simpa using IsLocalization.map_units (IntPrimeLocal p)
    (⟨(n : ℤ), hm⟩ : (characteristicPrime p).primeCompl)

/-- The universe lift does not change the prime-to-p unit criterion. -/
theorem isUnit_natCast_primeLocalRing (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hn : ¬ p ∣ n) : IsUnit (n : PrimeLocalRing.{u} p) := by
  simpa using (isUnit_natCast_intPrimeLocal p n hn).map
    (ULift.ringEquiv.symm : IntPrimeLocal p ≃+* PrimeLocalRing.{u} p)

/-- The specialized quasi-unit criterion for a p-local slice Burnside algebra.
Only its explicit mark values, table, and additive basis are required here. -/
theorem isUnit_of_primeTo_marks (p : ℕ) [Fact p.Prime]
    {B : Type v} [CommRing B] [Algebra (PrimeLocalRing.{u} p) B]
    (b : Module.Basis ι (PrimeLocalRing.{u} p) B)
    (mark : ι → B →ₐ[PrimeLocalRing.{u} p] PrimeLocalRing.{u} p)
    (hmark : (markMatrix b mark).det ≠ 0) (a : B)
    (n : ι → ℕ) (hn : ∀ i, ¬ p ∣ n i)
    (ha : ∀ i, mark i a = (n i : PrimeLocalRing.{u} p)) : IsUnit a := by
  apply isUnit_of_marks b mark hmark a
  intro i
  rw [ha]
  exact isUnit_natCast_primeLocalRing p (n i) (hn i)

end Sharpness.Burnside
