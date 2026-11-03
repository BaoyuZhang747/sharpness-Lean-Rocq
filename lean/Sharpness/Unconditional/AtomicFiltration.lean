import Sharpness.Unconditional.CollectionRestrictionZeroExtension
import Sharpness.Unconditional.ExtExactVanishing
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Finite atomic filtration of coefficient diagrams on ranked EI categories.
The induction removes a minimal nonzero isomorphism class via an actual
epimorphism to an extension by zero; its kernel is atomic. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.AtomicFiltration
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)

def after (Q : C) : ObjectProperty C := fun P => rank Q ≤ rank P ∧ ¬ Nonempty (P ≅ Q)

include rank_mono iso_of_rank in
theorem after_upward (Q : C) :
    ∀ {P T : C}, (P ⟶ T) → after rank Q P → after rank Q T := by
  intro P T f hP
  refine ⟨hP.1.trans (rank_mono f), ?_⟩
  rintro ⟨e⟩
  have hTP : rank T ≤ rank P := (rank_mono e.hom).trans hP.1
  haveI : IsIso f := iso_of_rank f (le_antisymm (rank_mono f) hTP)
  exact hP.2 ⟨(asIso f).trans e⟩

def remainder (M : CoefficientCategory R C) (Q : C) : CoefficientCategory R C :=
  ZeroExtension.coefficient R (after rank Q) (after_upward rank rank_mono iso_of_rank Q)
    ((after rank Q).ι.op ⋙ M)

def projection (M : CoefficientCategory R C) (Q : C) : M ⟶
    remainder R rank rank_mono iso_of_rank M Q :=
  ZeroExtension.unitMap R (after rank Q) (after_upward rank rank_mono iso_of_rank Q) M

instance projection_epi (M : CoefficientCategory R C) (Q : C) :
    Epi (projection R rank rank_mono iso_of_rank M Q) :=
  ZeroExtension.unitMap_epi R (after rank Q) (after_upward rank rank_mono iso_of_rank Q) M

def atomicPart (M : CoefficientCategory R C) (Q : C) : CoefficientCategory R C :=
  kernel (projection R rank rank_mono iso_of_rank M Q)

theorem atomicPart_zero_of_value_zero (M : CoefficientCategory R C) (Q P : C)
    (hP : IsZero (M.obj (op P))) :
    IsZero ((atomicPart R rank rank_mono iso_of_rank M Q).obj (op P)) := by
  let π := projection R rank rank_mono iso_of_rank M Q
  let E := (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op P)
  have hz : IsZero (kernel (π.app (op P))) := IsZero.of_mono (kernel.ι _) hP
  exact IsZero.of_iso hz (PreservesKernel.iso E π)

theorem atomicPart_zero_of_after (M : CoefficientCategory R C) (Q P : C)
    (hP : after rank Q P) :
    IsZero ((atomicPart R rank rank_mono iso_of_rank M Q).obj (op P)) := by
  let π := projection R rank rank_mono iso_of_rank M Q
  haveI : Mono (π.app (op P)) := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    exact congrFun hxy ⟨hP⟩)
  exact IsZero.of_iso (isZero_kernel_of_mono (π.app (op P)))
    (PreservesKernel.iso ((evaluation Cᵒᵖ (ModuleCat.{u} R)).obj (op P)) π)

theorem atomicPart_supported (M : CoefficientCategory R C) (Q : C)
    (minimal : ∀ P, rank P < rank Q → IsZero (M.obj (op P))) :
    ∀ P, ¬ Nonempty (P ≅ Q) →
      IsZero ((atomicPart R rank rank_mono iso_of_rank M Q).obj (op P)) := by
  intro P hP
  by_cases hlt : rank P < rank Q
  · exact atomicPart_zero_of_value_zero R rank rank_mono iso_of_rank M Q P (minimal P hlt)
  · exact atomicPart_zero_of_after R rank rank_mono iso_of_rank M Q P ⟨by omega, hP⟩

theorem remainder_zero_of_value_zero (M : CoefficientCategory R C) (Q P : C)
    (hP : IsZero (M.obj (op P))) :
    IsZero ((remainder R rank rank_mono iso_of_rank M Q).obj (op P)) := by
  haveI : Subsingleton (M.obj (op P)) := ModuleCat.subsingleton_of_isZero hP
  change IsZero (ModuleCat.of R (∀ _ : PLift (after rank Q P), M.obj (op P)))
  exact ModuleCat.isZero_of_subsingleton _

theorem remainder_zero_at_label (M : CoefficientCategory R C) (Q : C) :
    IsZero ((remainder R rank rank_mono iso_of_rank M Q).obj (op Q)) := by
  apply ZeroExtension.isZero_value_of_not
  exact fun h => h.2 ⟨Iso.refl Q⟩

theorem exists_minimal_nonzero (M : CoefficientCategory R C)
    (hne : ∃ P, ¬ IsZero (M.obj (op P))) :
    ∃ Q, ¬ IsZero (M.obj (op Q)) ∧
      ∀ P, rank P < rank Q → IsZero (M.obj (op P)) := by
  classical
  have hex : ∃ n : ℕ, ∃ P, rank P = n ∧ ¬ IsZero (M.obj (op P)) := by
    obtain ⟨P, hP⟩ := hne
    exact ⟨rank P, P, rfl, hP⟩
  obtain ⟨Q, hQ, hneQ⟩ := Nat.find_spec hex
  refine ⟨Q, hneQ, ?_⟩
  intro P hP
  by_contra hn
  exact Nat.find_min hex (hQ ▸ hP) ⟨P, rfl, hn⟩

variable [Fintype C]

def supportFinset (M : CoefficientCategory R C) : Finset C := by
  classical
  exact Finset.univ.filter (fun P => ¬ IsZero (M.obj (op P)))

theorem remainder_support_subset (M : CoefficientCategory R C) (Q : C) :
    supportFinset R (remainder R rank rank_mono iso_of_rank M Q) ⊆ supportFinset R M := by
  classical
  intro P hP
  simp only [supportFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
  exact fun hz => hP (remainder_zero_of_value_zero R rank rank_mono iso_of_rank M Q P hz)

theorem remainder_support_card_lt (M : CoefficientCategory R C) (Q : C)
    (hne : ¬ IsZero (M.obj (op Q))) :
    (supportFinset R (remainder R rank rank_mono iso_of_rank M Q)).card <
      (supportFinset R M).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨remainder_support_subset R rank rank_mono iso_of_rank M Q, ?_⟩
  intro heq
  have hQ : Q ∈ supportFinset R M := by simp [supportFinset, hne]
  rw [← heq] at hQ
  have hn := (Finset.mem_filter.mp hQ).2
  exact hn (remainder_zero_at_label R rank rank_mono iso_of_rank M Q)

include rank rank_mono iso_of_rank in
/-- Finite atomic reduction for all-degree higher-limit vanishing.
The only vanishing hypothesis concerns genuinely atomic diagrams. -/
theorem higherLimits_zero_of_atomic (W : C → Prop)
    (atomic : ∀ Q, W Q → ∀ A : CoefficientCategory R C,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))
    (M : CoefficientCategory R C)
    (supported : ∀ P, ¬ W P → IsZero (M.obj (op P))) :
    ∀ n, IsZero (higherLimit M n) := by
  classical
  have aux : ∀ d, ∀ A : CoefficientCategory R C, (supportFinset R A).card = d →
      (∀ P, ¬ W P → IsZero (A.obj (op P))) → ∀ n, IsZero (higherLimit A n) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A hsize hsupp
      by_cases hne : ∃ P, ¬ IsZero (A.obj (op P))
      · obtain ⟨Q, hQ, hmin⟩ := exists_minimal_nonzero R rank A hne
        have hWQ : W Q := by
          by_contra hn
          exact hQ (hsupp Q hn)
        let B := remainder R rank rank_mono iso_of_rank A Q
        let K := atomicPart R rank rank_mono iso_of_rank A Q
        have hB : ∀ n, IsZero (higherLimit B n) :=
          ih (supportFinset R B).card (by
            rw [← hsize]
            exact remainder_support_card_lt R rank rank_mono iso_of_rank A Q hQ)
            B rfl (fun P hP =>
              remainder_zero_of_value_zero R rank rank_mono iso_of_rank A Q P (hsupp P hP))
        have hK : ∀ n, IsZero (higherLimit K n) :=
          atomic Q hWQ K (atomicPart_supported R rank rank_mono iso_of_rank A Q hmin)
        let π := projection R rank rank_mono iso_of_rank A Q
        let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
        have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
        intro n
        exact ext_isZero_of_shortExact R (constantCoefficient R C) S hS n (hK n) (hB n)
      · have hz : IsZero A := by
          apply Functor.isZero
          intro P
          by_contra hp
          exact hne ⟨P.unop, hp⟩
        exact higherLimit_isZero_of_isZero R A hz
  exact aux _ M rfl supported

end Sharpness.AtomicFiltration
