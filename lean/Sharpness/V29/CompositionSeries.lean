import Sharpness.MackeySubquotients

/-! Finite composition series of actual full Mackey modules.  Each step
selects a simple Mackey submodule and continues with its actual objectwise
quotient.  Thus the factors belong to this particular module, rather than
to a globally quantified class of simple Mackey modules. -/
set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.MackeyModule.V29
open CategoryTheory
open scoped BigOperators

variable {k : Type u} [Field k] {C : Type v} [Category.{v} C]
    {B : MackeyShape C}

def topSubfunctor (M : MackeyModule.{u,v,w} k C B) : M.Subfunctor where
  obj _ := ⊤
  pull_closed := by intros; exact Submodule.mem_top
  push_closed := by intros; exact Submodule.mem_top

/-- A full subfunctor of a full subfunctor is a full subfunctor of M.
The actual component is the image under the subtype inclusion. -/
def nestedImage (M : MackeyModule.{u,v,w} k C B) (N : M.Subfunctor)
    (P : (M.submodule N).Subfunctor) : M.Subfunctor where
  obj i := (P.obj i).map (N.obj i).subtype
  pull_closed := by
    intro i j f x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(M.submodule N).pull f y, P.pull_closed f hy, rfl⟩
  push_closed := by
    intro i j f x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(M.submodule N).push f y, P.push_closed f hy, rfl⟩

theorem nestedImage_dimension [Fintype C]
    (M : MackeyModule.{u,v,w} k C B)
    [∀ i, FiniteDimensional k (M.Value i)] (N : M.Subfunctor)
    (P : (M.submodule N).Subfunctor) :
    (M.submodule (nestedImage M N P)).linearSystem.totalDimension =
      ((M.submodule N).submodule P).linearSystem.totalDimension := by
  unfold LinearSystem.totalDimension
  apply Finset.sum_congr rfl
  intro i _
  exact Submodule.finrank_map_subtype_eq (N.obj i) (P.obj i)

theorem totalDimension_zero_of_values_zero [Fintype C]
    (M : MackeyModule.{u,v,w} k C B)
    [∀ i, FiniteDimensional k (M.Value i)]
    (hz : ∀ i, ∀ x : M.Value i, x = 0) :
    M.linearSystem.totalDimension = 0 := by
  unfold LinearSystem.totalDimension
  apply Finset.sum_eq_zero
  intro i _
  change Module.finrank k (M.Value i) = 0
  letI : Subsingleton (M.Value i) := ⟨fun x y => (hz i x).trans (hz i y).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- A nonzero finite-dimensional full Mackey module has a simple full
Mackey subfunctor.  We minimize the positive sum of the component dimensions.
No classification or acyclicity theorem is used. -/
theorem exists_simple_subfunctor [Fintype C]
    (M : MackeyModule.{u,v,w} k C B)
    [∀ i, FiniteDimensional k (M.Value i)]
    (hnz : ∃ i, ∃ x : M.Value i, x ≠ 0) :
    ∃ N : M.Subfunctor, (M.submodule N).IsSimple := by
  classical
  have ht : ¬ ∀ i, (topSubfunctor M).obj i = ⊥ := by
    obtain ⟨i, x, hx⟩ := hnz
    intro h
    have hm : x ∈ (topSubfunctor M).obj i := Submodule.mem_top
    rw [h i] at hm
    exact hx hm
  have hpos := M.linearSystem.sub_totalDimension_pos
    (M.toLinearSubsystem (topSubfunctor M)) ht
  have hex : ∃ n : ℕ, ∃ N : M.Subfunctor,
      (M.submodule N).linearSystem.totalDimension = n ∧ 0 < n :=
    ⟨_, topSubfunctor M, rfl, hpos⟩
  obtain ⟨N, hdim, hpositive⟩ := Nat.find_spec hex
  refine ⟨N, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hz := totalDimension_zero_of_values_zero (M.submodule N) h
    omega
  · intro P
    by_cases hb : ∀ i, P.obj i = ⊥
    · exact Or.inl hb
    · right
      by_contra hp
      have hs := (M.submodule N).linearSystem.sub_totalDimension_pos
        ((M.submodule N).toLinearSubsystem P) hb
      have hq := (M.submodule N).linearSystem.quotient_totalDimension_pos
        ((M.submodule N).toLinearSubsystem P) hp
      have hsum := (M.submodule N).linearSystem.totalDimension_sub_add_quotient
        ((M.submodule N).toLinearSubsystem P)
      have hmin : Nat.find hex ≤
          (M.submodule (nestedImage M N P)).linearSystem.totalDimension :=
        Nat.find_min' hex ⟨nestedImage M N P, rfl, by
          rw [nestedImage_dimension]
          exact hs⟩
      rw [nestedImage_dimension] at hmin
      change ((M.submodule N).submodule P).linearSystem.totalDimension +
        ((M.submodule N).quotient P).linearSystem.totalDimension =
        (M.submodule N).linearSystem.totalDimension at hsum
      change 0 < ((M.submodule N).quotient P).linearSystem.totalDimension at hq
      omega

/-- A finite composition series, encoded by successive simple submodules
and the resulting quotients.  It begins at M and ends in the zero module.
Pulling each successive submodule back through the preceding quotient maps
gives the usual increasing filtration of M. -/
inductive CompositionSeries : MackeyModule.{u,v,w} k C B → Type (max u v (w + 1))
  | nil (M : MackeyModule.{u,v,w} k C B)
      (zero : ∀ i, ∀ x : M.Value i, x = 0) : CompositionSeries M
  | cons (M : MackeyModule.{u,v,w} k C B) (N : M.Subfunctor)
      (simple : (M.submodule N).IsSimple)
      (tail : CompositionSeries (M.quotient N)) : CompositionSeries M

/-- Finite-dimensional values at finitely many objects give a finite
composition series.  The quotient dimension strictly decreases at every step. -/
theorem nonempty_compositionSeries [Fintype C]
    (M : MackeyModule.{u,v,w} k C B)
    [∀ i, FiniteDimensional k (M.Value i)] : Nonempty (CompositionSeries M) := by
  classical
  have aux : ∀ n, ∀ (A : MackeyModule.{u,v,w} k C B)
      [∀ i, FiniteDimensional k (A.Value i)],
      A.linearSystem.totalDimension = n → Nonempty (CompositionSeries A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ hdim
      by_cases hz : ∀ i, ∀ x : A.Value i, x = 0
      · exact ⟨CompositionSeries.nil A hz⟩
      · have hnz : ∃ i, ∃ x : A.Value i, x ≠ 0 := by
          push Not at hz
          exact hz
        obtain ⟨N, hN⟩ := exists_simple_subfunctor A hnz
        have hnonzero : ¬ ∀ i, N.obj i = ⊥ := by
          obtain ⟨i, x, hx⟩ := hN.1
          intro h
          have hm : (show N.obj i from x).val ∈ (⊥ : Submodule k (A.Value i)) :=
            (le_of_eq (h i)) x.property
          exact hx (Subtype.ext hm)
        have hp := A.linearSystem.sub_totalDimension_pos (A.toLinearSubsystem N) hnonzero
        have hd := A.linearSystem.totalDimension_sub_add_quotient (A.toLinearSubsystem N)
        change (A.submodule N).linearSystem.totalDimension +
          (A.quotient N).linearSystem.totalDimension = A.linearSystem.totalDimension at hd
        change 0 < (A.submodule N).linearSystem.totalDimension at hp
        obtain ⟨tail⟩ := ih (A.quotient N).linearSystem.totalDimension (by omega)
          (A.quotient N) rfl
        exact ⟨CompositionSeries.cons A N hN tail⟩
  exact aux M.linearSystem.totalDimension M rfl

noncomputable def compositionSeries [Fintype C]
    (M : MackeyModule.{u,v,w} k C B)
    [∀ i, FiniteDimensional k (M.Value i)] : CompositionSeries M :=
  Classical.choice (nonempty_compositionSeries M)

namespace CompositionSeries

def factors : {M : MackeyModule.{u,v,w} k C B} → CompositionSeries M →
    List (MackeyModule.{u,v,w} k C B)
  | _, .nil _ _ => []
  | _, .cons M N _ tail => M.submodule N :: factors tail

theorem factors_simple {M : MackeyModule.{u,v,w} k C B}
    (s : CompositionSeries M) : ∀ A ∈ s.factors, A.IsSimple := by
  induction s with
  | nil M hz => simp [factors]
  | cons M N hs tail ih =>
    intro A hA
    simp only [factors, List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact hs
    · exact ih A hA

end CompositionSeries
end Sharpness.MackeyModule.V29
