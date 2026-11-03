import Sharpness.ReferenceInputs
import Sharpness.IndexedGenerators
import Sharpness.FusionCentricClosure

/-!
The minimal label and centric-support assertions for simple full Mackey
functors. These assertions follow from the actual Mackey normal form and
simplicity; no classification theorem is assumed.
-/
set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.MackeyModule
open CategoryTheory

variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} (M : MackeyModule.{u,v,w} R C B)

/-- A nonzero Mackey functor has a value of least rank. -/
theorem exists_minimal_nonzero (hne : ∃ P, ∃ x : M.Value P, x ≠ 0) :
    ∃ Q, (∃ x : M.Value Q, x ≠ 0) ∧
      ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ P, B.rank P = n ∧ ∃ x : M.Value P, x ≠ 0 := by
    obtain ⟨P, x, hx⟩ := hne
    exact ⟨B.rank P, P, rfl, x, hx⟩
  obtain ⟨Q, hQ, hx⟩ := Nat.find_spec hex
  refine ⟨Q, hx, ?_⟩
  intro P hP x
  by_contra hx
  have hmin := Nat.find_min hex (hQ ▸ hP)
  exact hmin ⟨P, rfl, x, hx⟩

/-- At a minimal nonzero value, an invariant submodule generates no larger
submodule at that same value: every nonzero span is an automorphism. -/
theorem indexedGenerated_at_minimal_le (Q : C)
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    (A : Submodule R (M.Value Q))
    (stable : ∀ g : Aut Q, ∀ x ∈ A, M.push g.hom x ∈ A) :
    M.indexedGeneratedValue (fun _ : A => Q) (fun x => x.val) Q ≤ A := by
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨x, s, rfl⟩ := hy
  change M.normalMap s x.val ∈ A
  rcases lt_or_eq_of_le (B.rank_mono s.left) with hlt | heq
  · have hz := small_zero s.apex hlt (M.pull s.left x.val)
    simp only [normalMap, LinearMap.comp_apply, hz, map_zero]
    exact A.zero_mem
  · haveI : IsIso s.left := B.iso_of_rank s.left heq
    haveI : IsIso s.right := B.iso_of_rank s.right heq
    let g : Aut Q := (asIso s.left).symm.trans (asIso s.right)
    have hg := stable g x.val x.property
    change M.push (inv s.left ≫ s.right) x.val ∈ A at hg
    simpa only [normalMap, M.pull_iso, M.push_comp, LinearMap.comp_apply] using hg

/-- Simplicity of the whole Mackey functor implies simplicity of the
automorphism representation at any minimal nonzero object. -/
theorem simple_at_minimal (Q : C)
    (small_zero : ∀ P, B.rank P < B.rank Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple)
    (A : Submodule R (M.Value Q))
    (stable : ∀ g : Aut Q, ∀ x ∈ A, M.push g.hom x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  let N := M.indexedGeneratedSubfunctor (fun _ : A => Q) (fun x => x.val)
  have hAN : A ≤ N.obj Q := by
    intro x hx
    exact M.mem_indexedGeneratedValue (fun _ : A => Q) (fun x => x.val) ⟨x, hx⟩
  have hNA : N.obj Q ≤ A := M.indexedGenerated_at_minimal_le Q small_zero A stable
  rcases simple.2 N with hbot | htop
  · left
    apply bot_unique
    exact hAN.trans_eq (hbot Q)
  · right
    apply top_unique
    exact (htop Q).symm.trans_le hNA

end Sharpness.MackeyModule

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]

/-- The minimal label used in the proof is constructed from simplicity. -/
def simpleLabel (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (simple : M.IsSimple) : F.SimpleLabel M := by
  let Q := Classical.choose (M.exists_minimal_nonzero simple.1)
  have hQ := (Classical.choose_spec (M.exists_minimal_nonzero simple.1)).1
  have small_zero := (Classical.choose_spec (M.exists_minimal_nonzero simple.1)).2
  exact
    { Q := Q
      simple := simple
      nonzero := hQ
      small_zero := small_zero
      simple_at_Q := fun A hA => M.simple_at_minimal Q small_zero simple A hA }

/-- A morphism with centric source also has centric target. -/
theorem centric_of_orbit_hom {P Q : F.Orbit} (f : P ⟶ Q)
    (hP : F.IsCentric P.as.subgroup) : F.IsCentric Q.as.subgroup := by
  have hi := F.isoSystem.centricIn_of_iso (F.groupEquivOfOrbitIso (F.arrowImageIso f))
    (F.groupEquivOfOrbitIso_allowed (F.arrowImageIso f)) hP
  exact F.centric_overgroup hi (F.arrowImage_le f)

/-- A simple Mackey functor with centric minimal label vanishes off the
centric collection, since it is generated from that label by transfers. -/
theorem simple_zero_of_noncentric (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M) (centric : F.IsCentric label.Q.as.subgroup)
    (P : F.Orbit) (noncentric : ¬ F.IsCentric P.as.subgroup) (x : M.Value P) : x = 0 := by
  have hgen := M.transfer_generation label.Q label.small_zero label.simple label.nonzero P
  have hbot : M.generated label.Q P = ⊥ := by
    apply bot_unique
    refine iSup_le fun s => ?_
    exact (noncentric (F.centric_of_orbit_hom (s.2.1.hom ≫ s.2.2) centric)).elim
  have hx : x ∈ M.generated label.Q P := by rw [hgen]; trivial
  simpa only [hbot, Submodule.mem_bot] using hx

/-- Unconditional construction of the DP minimal-label and support package.
No saturation, characteristic, or finite-dimensionality assumption is needed. -/
def diazParkInputs : F.DiazParkInputs (k := k) where
  propositions_3_1_3_2 M simple := ⟨F.simpleLabel M simple⟩
  proposition_3_3 := F.simple_zero_of_noncentric

end Sharpness.FusionSystem
