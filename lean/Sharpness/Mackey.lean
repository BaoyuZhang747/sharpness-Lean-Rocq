import Sharpness.LinearCore

/-!
An abstract full Mackey formula on a ranked category, and the complete
generation/detection proof for simple Mackey modules.

The formula includes EVERY supplied double-coset span; no centric truncation
is allowed. A fusion orbit category must still be constructed and connected
to this interface. The interface itself contains no generation or detection
conclusion, and neither conclusion is an external axiom.
-/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory
open scoped BigOperators

structure MackeySpan (C : Type v) [Category.{v} C] (P Q : C) where
  apex : C
  left : apex ⟶ P
  right : apex ⟶ Q

/-- Rank and double-coset span data. In a fusion orbit category rank is
subgroup order and the spans are the usual intersection/conjugation spans. -/
structure MackeyShape (C : Type v) [Category.{v} C] where
  rank : C → ℕ
  rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q
  iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f
  Term : ∀ {P Q T : C}, (P ⟶ T) → (Q ⟶ T) → Type v
  termFintype : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T), Fintype (Term f g)
  span : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T), Term f g → MackeySpan C P Q

attribute [instance] MackeyShape.termFintype

structure MackeyModule (R : Type u) [Ring R] (C : Type v) [Category.{v} C]
    (B : MackeyShape C) where
  Value : C → Type w
  valueAddCommGroup : ∀ P, AddCommGroup (Value P)
  valueModule : ∀ P, Module R (Value P)
  pull : ∀ {P Q : C}, (P ⟶ Q) → Value Q →ₗ[R] Value P
  push : ∀ {P Q : C}, (P ⟶ Q) → Value P →ₗ[R] Value Q
  pull_id : ∀ P, pull (𝟙 P) = LinearMap.id
  push_id : ∀ P, push (𝟙 P) = LinearMap.id
  pull_comp : ∀ {P Q T : C} (f : P ⟶ Q) (g : Q ⟶ T),
    pull (f ≫ g) = (pull f).comp (pull g)
  push_comp : ∀ {P Q T : C} (f : P ⟶ Q) (g : Q ⟶ T),
    push (f ≫ g) = (push g).comp (push f)
  pull_iso : ∀ {P Q : C} (f : P ⟶ Q) [IsIso f], pull f = push (inv f)
  mackey : ∀ {P Q T : C} (f : P ⟶ T) (g : Q ⟶ T),
    (pull f).comp (push g) =
      ∑ i : B.Term f g, (push (B.span f g i).left).comp (pull (B.span f g i).right)

attribute [instance] MackeyModule.valueAddCommGroup MackeyModule.valueModule

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B)

structure Subfunctor where
  obj : ∀ P, Submodule R (M.Value P)
  pull_closed : ∀ {P Q : C} (f : P ⟶ Q) {x}, x ∈ obj Q → M.pull f x ∈ obj P
  push_closed : ∀ {P Q : C} (f : P ⟶ Q) {x}, x ∈ obj P → M.push f x ∈ obj Q

def IsSimple : Prop :=
  (∃ P, ∃ x : M.Value P, x ≠ 0) ∧
  ∀ N : M.Subfunctor, (∀ P, N.obj P = ⊥) ∨ (∀ P, N.obj P = ⊤)

variable (Q : C)

/-- An isomorphic minimal object together with a morphism into P. -/
abbrev SeedMap (P : C) := Σ L : C, (Q ≅ L) × (L ⟶ P)

def generated (P : C) : Submodule R (M.Value P) :=
  ⨆ s : SeedMap Q P, LinearMap.range (M.push s.2.2)

def detectedKernel (P : C) : Submodule R (M.Value P) :=
  ⨅ s : SeedMap Q P, LinearMap.ker (M.pull s.2.2)

theorem rank_eq_of_iso {P L : C} (e : P ≅ L) : B.rank P = B.rank L :=
  le_antisymm (B.rank_mono e.hom) (B.rank_mono e.inv)

theorem push_mem_generated {P L : C} (e : Q ≅ L) (f : L ⟶ P) (x : M.Value L) :
    M.push f x ∈ M.generated Q P := by
  exact le_iSup (fun s : SeedMap Q P => LinearMap.range (M.push s.2.2))
    ⟨L, e, f⟩ ⟨x, rfl⟩

theorem generated_push_closed {P T : C} (a : P ⟶ T) {x : M.Value P}
    (hx : x ∈ M.generated Q P) : M.push a x ∈ M.generated Q T := by
  have h : M.generated Q P ≤ (M.generated Q T).comap (M.push a) := by
    refine iSup_le fun s y hy => ?_
    obtain ⟨z, rfl⟩ := hy
    change M.push a (M.push s.2.2 z) ∈ M.generated Q T
    rw [← LinearMap.comp_apply, ← M.push_comp]
    exact M.push_mem_generated Q s.2.1 (s.2.2 ≫ a) z
  exact h hx

theorem generated_pull_closed
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    {P T : C} (a : P ⟶ T) {x : M.Value T}
    (hx : x ∈ M.generated Q T) : M.pull a x ∈ M.generated Q P := by
  have h : M.generated Q T ≤ (M.generated Q P).comap (M.pull a) := by
    refine iSup_le fun s y hy => ?_
    obtain ⟨z, rfl⟩ := hy
    change M.pull a (M.push s.2.2 z) ∈ M.generated Q P
    have hm := LinearMap.congr_fun (M.mackey a s.2.2) z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hm
    rw [hm]
    apply Submodule.sum_mem
    intro i _
    let t := B.span a s.2.2 i
    have hr : B.rank t.apex ≤ B.rank Q := by
      exact (B.rank_mono t.right).trans_eq (rank_eq_of_iso s.2.1).symm
    rcases lt_or_eq_of_le hr with hlt | heq
    · have hz := small_zero t.apex hlt (M.pull t.right z)
      change M.push t.left (M.pull t.right z) ∈ M.generated Q P
      rw [hz, map_zero]
      exact Submodule.zero_mem _
    · haveI : IsIso t.right := B.iso_of_rank t.right
        (heq.trans (rank_eq_of_iso s.2.1))
      exact M.push_mem_generated Q (s.2.1.trans (asIso t.right).symm)
        t.left (M.pull t.right z)
  exact h hx

def generatedSubfunctor
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0) : M.Subfunctor where
  obj := M.generated Q
  push_closed := M.generated_push_closed Q
  pull_closed := M.generated_pull_closed Q small_zero

theorem mem_detectedKernel_iff {P : C} {x : M.Value P} :
    x ∈ M.detectedKernel Q P ↔ ∀ s : SeedMap Q P, M.pull s.2.2 x = 0 := by
  simp only [detectedKernel, Submodule.mem_iInf, LinearMap.mem_ker]

theorem detectedKernel_pull_closed {P T : C} (a : P ⟶ T) {x : M.Value T}
    (hx : x ∈ M.detectedKernel Q T) : M.pull a x ∈ M.detectedKernel Q P := by
  rw [M.mem_detectedKernel_iff Q] at hx ⊢
  intro s
  have h := hx ⟨s.1, s.2.1, s.2.2 ≫ a⟩
  simpa only [M.pull_comp, LinearMap.comp_apply] using h

theorem detectedKernel_push_closed
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    {P T : C} (a : P ⟶ T) {x : M.Value P}
    (hx : x ∈ M.detectedKernel Q P) : M.push a x ∈ M.detectedKernel Q T := by
  rw [M.mem_detectedKernel_iff Q] at hx ⊢
  intro s
  have hm := LinearMap.congr_fun (M.mackey s.2.2 a) x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hm
  rw [hm]
  apply Finset.sum_eq_zero
  intro i _
  let t := B.span s.2.2 a i
  have hr : B.rank t.apex ≤ B.rank Q :=
    (B.rank_mono t.left).trans_eq (rank_eq_of_iso s.2.1).symm
  rcases lt_or_eq_of_le hr with hlt | heq
  · have hz := small_zero t.apex hlt (M.pull t.right x)
    change M.push t.left (M.pull t.right x) = 0
    rw [hz, map_zero]
  · haveI : IsIso t.left := B.iso_of_rank t.left
      (heq.trans (rank_eq_of_iso s.2.1))
    have hz := hx ⟨t.apex, s.2.1.trans (asIso t.left).symm, t.right⟩
    change M.push t.left (M.pull t.right x) = 0
    rw [hz, map_zero]

def detectedSubfunctor
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0) : M.Subfunctor where
  obj := M.detectedKernel Q
  pull_closed := M.detectedKernel_pull_closed Q
  push_closed := M.detectedKernel_push_closed Q small_zero

/-- The generation half of `lem:generators` on the abstract ranked Mackey
category, derived from the full formula and simplicity. -/
theorem transfer_generation
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple)
    (nonzero_at_Q : ∃ x : M.Value Q, x ≠ 0) :
    ∀ P, M.generated Q P = ⊤ := by
  rcases simple.2 (M.generatedSubfunctor Q small_zero) with h | h
  · obtain ⟨x, hx⟩ := nonzero_at_Q
    have hm := M.push_mem_generated Q (Iso.refl Q) (𝟙 Q) x
    rw [M.push_id] at hm
    have hbot : M.generated Q Q = ⊥ := h Q
    rw [hbot] at hm
    exact (hx hm).elim
  · exact h

theorem detectedKernel_eq_bot
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple)
    (nonzero_at_Q : ∃ x : M.Value Q, x ≠ 0) :
    ∀ P, M.detectedKernel Q P = ⊥ := by
  rcases simple.2 (M.detectedSubfunctor Q small_zero) with h | h
  · exact h
  · obtain ⟨x, hx⟩ := nonzero_at_Q
    have hm : x ∈ M.detectedKernel Q Q := by
      have htop : M.detectedKernel Q Q = ⊤ := h Q
      simp [htop]
    have hz := (M.mem_detectedKernel_iff Q).mp hm ⟨Q, Iso.refl Q, 𝟙 Q⟩
    rw [M.pull_id] at hz
    exact (hx hz).elim

/-- The detection half of `lem:generators`, with an actual product map. -/
theorem restriction_detection
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple)
    (nonzero_at_Q : ∃ x : M.Value Q, x ≠ 0) (P : C) :
    Function.Injective (restrictionProduct
      (fun s : SeedMap Q P => M.pull s.2.2)) := by
  rw [restrictionProduct_injective_iff]
  intro x hx
  have hm := (M.mem_detectedKernel_iff Q).mpr hx
  rw [M.detectedKernel_eq_bot Q small_zero simple nonzero_at_Q P] at hm
  exact hm

end MackeyModule
end Sharpness
