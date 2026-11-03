import Mathlib

/-! The zero-page consequence of an actual first-quadrant spectral
sequence with a finite abutment filtration. This deduction is proved
here; the reference interface supplies pages and convergence, not a
vanishing implication. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

/-- Finite convergence data in total degree n. The stable page n+2 is
sufficient in the first quadrant. Quotients are actual module quotients. -/
structure FiniteSpectralConvergence
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (A : ℕ → ModuleCat.{u} R) where
  filtration : ∀ n, ℕ → Submodule R (A n)
  antitone : ∀ n, Antitone (filtration n)
  start : ∀ n, filtration n 0 = ⊤
  stop : ∀ n, filtration n (n+1) = ⊥
  graded : ∀ (n i : ℕ) (_ : i ≤ n),
    (ModuleCat.of R (filtration n i ⧸ (filtration n (i+1)).comap (filtration n i).subtype) ≅
      (E.page (n+2) (by omega)).X (i, n-i))

theorem spectralSequence_pages_zero
    (E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R))
    (zero : ∀ pq, IsZero ((E.page 2).X pq)) :
    ∀ (r : ℕ) pq, IsZero ((E.page (r+2) (by omega)).X pq) := by
  intro r
  induction r with
  | zero => exact zero
  | succ r ih =>
    intro pq
    have hz : IsZero ((E.page (r+2) (by omega)).homology pq) :=
      (HomologicalComplex.ExactAt.of_isZero (ih pq)).isZero_homology
    exact IsZero.of_iso hz (E.iso (r+2) ((r+1 : ℕ)+2) pq (by omega) (by omega)).symm

theorem submodule_le_of_quotient_isZero
    {V : Type u} [AddCommGroup V] [Module R V] (P Q : Submodule R V)
    (zero : IsZero (ModuleCat.of R (P ⧸ Q.comap P.subtype))) : P ≤ Q := by
  haveI : Subsingleton (P ⧸ Q.comap P.subtype) := ModuleCat.isZero_iff_subsingleton.mp zero
  intro x hx
  have hz : (Submodule.Quotient.mk (⟨x, hx⟩ : P) : P ⧸ Q.comap P.subtype) = 0 :=
    Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero (Q.comap P.subtype)).mp hz

theorem FiniteSpectralConvergence.abutment_zero
    {E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R)}
    {A : ℕ → ModuleCat.{u} R} (conv : FiniteSpectralConvergence E A)
    (zero : ∀ pq, IsZero ((E.page 2).X pq)) (n : ℕ) : IsZero (A n) := by
  have step : ∀ i, i ≤ n → conv.filtration n i ≤ conv.filtration n (i+1) := by
    intro i hi
    apply submodule_le_of_quotient_isZero
    exact IsZero.of_iso (spectralSequence_pages_zero E zero n (i, n-i)) (conv.graded n i hi)
  have alltop : ∀ i, i ≤ n+1 → conv.filtration n i = ⊤ := by
    intro i
    induction i with
    | zero => intro _; exact conv.start n
    | succ i ih =>
      intro hi
      apply top_unique
      calc
        ⊤ = conv.filtration n i := (ih (by omega)).symm
        _ ≤ conv.filtration n (i+1) := step i (by omega)
  have hb : (⊥ : Submodule R (A n)) = ⊤ := (conv.stop n).symm.trans (alltop (n+1) le_rfl)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : x ∈ (⊥ : Submodule R (A n)) := hb.symm ▸ Submodule.mem_top
  exact hx

end Sharpness
