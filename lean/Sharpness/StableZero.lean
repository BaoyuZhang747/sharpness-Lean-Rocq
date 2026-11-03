import Sharpness.LinearCore

/-!
The mathematical deduction in `lem:stable-zero`, expressed on actual
subgroups, actual group isomorphisms, actual centralizers and linear maps.
The two earlier manuscript results (restriction detection and the
centralizer-zero lemma) are explicit hypotheses of this deduction.
This file does not claim to have proved those two results for full Mackey
functors merely by accepting their conclusions as inputs.
-/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness

/-- The isomorphism part of a fusion category. Saturation is not encoded here.
It is deliberately named an iso system rather than a saturated fusion system. -/
structure FusionIsoSystem (S : Type u) [Group S] where
  Allowed : ∀ {P Q : Subgroup S}, (P ≃* Q) → Prop
  id_mem : ∀ P : Subgroup S, Allowed (MulEquiv.refl P)
  comp_mem : ∀ {P Q T : Subgroup S} (e : P ≃* Q) (f : Q ≃* T),
    Allowed e → Allowed f → Allowed (e.trans f)
  inv_mem : ∀ {P Q : Subgroup S} (e : P ≃* Q), Allowed e → Allowed e.symm

namespace FusionIsoSystem
variable {S : Type u} [Group S] (F : FusionIsoSystem S)

def IsConjugate (Q L : Subgroup S) : Prop := ∃ e : Q ≃* L, F.Allowed e

/-- Centricity inside T, using the actual centralizer subgroup in S.
For a fusion system over T its isomorphisms have endpoints contained in T. -/
def CentricIn (T P : Subgroup S) : Prop :=
  ∀ (P' : Subgroup S), P' ≤ T → ∀ e : P ≃* P',
    F.Allowed e → Subgroup.centralizer (P' : Set S) ⊓ T ≤ P'

theorem centricIn_of_iso {T P Q : Subgroup S} (e : P ≃* Q)
    (he : F.Allowed e) (hP : F.CentricIn T P) : F.CentricIn T Q := by
  intro L hL f hf
  exact hP L hL (e.trans f) (F.comp_mem e f he hf)

theorem centricIn_iff_of_iso {T P Q : Subgroup S} (e : P ≃* Q)
    (he : F.Allowed e) : F.CentricIn T P ↔ F.CentricIn T Q := by
  constructor
  · exact F.centricIn_of_iso e he
  · exact F.centricIn_of_iso e.symm (F.inv_mem e he)

theorem not_centricIn_witness {T P : Subgroup S} (h : ¬ F.CentricIn T P) :
    ∃ (L : Subgroup S) (_ : L ≤ T) (e : P ≃* L),
      F.Allowed e ∧ ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L := by
  classical
  unfold CentricIn at h
  push Not at h
  obtain ⟨L, hLT, e, he, hbad⟩ := h
  exact ⟨L, hLT, e, he, hbad⟩

end FusionIsoSystem

section StableZero
variable {R : Type v} [Ring R] {S : Type u} [Group S]
    (F H : FusionIsoSystem S) (T Q : Subgroup S)
    (V : Subgroup S → Type w) [∀ L, AddCommGroup (V L)] [∀ L, Module R (V L)]

/-- The index set of the detecting restrictions at T. -/
def MinimalInside : Type u := {L : Subgroup S // L ≤ T ∧ F.IsConjugate Q L}

variable (res : ∀ (L : Subgroup S), L ≤ T → V T →ₗ[R] V L)
    (isoPull : ∀ {L K : Subgroup S} (e : L ≃* K), F.Allowed e → V K →ₗ[R] V L)

def StableElement (x : V T) : Prop :=
  ∀ (L K : Subgroup S) (hL : L ≤ T) (hK : K ≤ T)
    (e : L ≃* K) (_heH : H.Allowed e) (heF : F.Allowed e),
    isoPull e heF (res K hK x) = res L hL x

/-- `lem:stable-zero`: the degree-zero vanishing argument, including the
noncentric-conjugate witness. All its unproved manuscript dependencies are
visible as individual hypotheses, not opaque structure fields. -/
theorem stable_element_eq_zero
    (subsystem : ∀ {L K : Subgroup S} (e : L ≃* K), H.Allowed e → F.Allowed e)
    (centric_inclusion : ∀ L, L ≤ T → H.CentricIn T L → F.CentricIn ⊤ L)
    (noncentric : ¬ F.CentricIn ⊤ Q)
    (detects : Function.Injective (restrictionProduct
      (fun L : MinimalInside F T Q => res L.val L.property.1)))
    (centralizer_zero : ∀ (L : Subgroup S) (hL : L ≤ T),
      F.IsConjugate Q L → (¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) →
        res L hL = 0)
    (x : V T) (hx : StableElement F H T V res isoPull x) : x = 0 := by
  apply (restrictionProduct_injective_iff _).mp detects x
  intro L
  have hLF : ¬ F.CentricIn ⊤ L.val := by
    intro hc
    obtain ⟨e, he⟩ := L.property.2
    exact noncentric ((F.centricIn_iff_of_iso e he).mpr hc)
  have hLH : ¬ H.CentricIn T L.val := by
    intro hc
    exact hLF (centric_inclusion L.val L.property.1 hc)
  obtain ⟨K, hKT, e, heH, hbad⟩ := H.not_centricIn_witness hLH
  have heF := subsystem e heH
  have hKmin : F.IsConjugate Q K := by
    obtain ⟨e0, he0⟩ := L.property.2
    exact ⟨e0.trans e, F.comp_mem e0 e he0 heF⟩
  have hz := centralizer_zero K hKT hKmin hbad
  have hs := hx L.val K L.property.1 hKT e heH heF
  rw [hz, LinearMap.zero_apply, map_zero] at hs
  exact hs.symm

end StableZero
end Sharpness
