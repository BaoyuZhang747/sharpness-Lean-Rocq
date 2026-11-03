import Sharpness.LinearCore

/-!
Finite-dimensional reduction in `lem:arbitrary`, Step 1.
Subobjects and quotients are constructed here. The induction uses the sum
of the actual dimensions of all values. The property being propagated must
be zero on zero systems and closed under extensions; for higher limits the
latter property comes from their long exact sequence, not from this lemma.
-/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness.LinearSystem
open scoped BigOperators
variable {k : Type u} [Field k] {I : Type v}

def subSystem (M : LinearSystem.{u,v,w} k I) (N : M.Subsystem) :
    LinearSystem k I where
  Value i := N.obj i
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  Operation := M.Operation
  act a :=
    { toFun := fun x => ⟨M.act a x.val, N.closed a x.property⟩
      map_add' := fun x y => Subtype.ext (map_add (M.act a) x.val y.val)
      map_smul' := fun r x => Subtype.ext (map_smul (M.act a) r x.val) }

def quotientSystem (M : LinearSystem.{u,v,w} k I) (N : M.Subsystem) :
    LinearSystem k I where
  Value i := M.Value i ⧸ N.obj i
  valueAddCommGroup _ := inferInstance
  valueModule _ := inferInstance
  Operation := M.Operation
  act := fun {i j} a => (N.obj i).mapQ (N.obj j) (M.act a)
    (fun _ hx => N.closed a hx)

instance subSystem_finite (M : LinearSystem.{u,v,w} k I) (N : M.Subsystem)
    [∀ i, FiniteDimensional k (M.Value i)] (i : I) :
    FiniteDimensional k ((M.subSystem N).Value i) := by
  change FiniteDimensional k (N.obj i)
  infer_instance

instance quotientSystem_finite (M : LinearSystem.{u,v,w} k I) (N : M.Subsystem)
    [∀ i, FiniteDimensional k (M.Value i)] (i : I) :
    FiniteDimensional k ((M.quotientSystem N).Value i) := by
  change FiniteDimensional k (M.Value i ⧸ N.obj i)
  infer_instance

def totalDimension [Fintype I] (M : LinearSystem.{u,v,w} k I)
    [∀ i, FiniteDimensional k (M.Value i)] : ℕ := ∑ i, Module.finrank k (M.Value i)

theorem totalDimension_sub_add_quotient [Fintype I]
    (M : LinearSystem.{u,v,w} k I) [∀ i, FiniteDimensional k (M.Value i)]
    (N : M.Subsystem) :
    (M.subSystem N).totalDimension + (M.quotientSystem N).totalDimension =
      M.totalDimension := by
  unfold totalDimension
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change Module.finrank k (N.obj i) + Module.finrank k (M.Value i ⧸ N.obj i) = _
  simpa only [Nat.add_comm] using (N.obj i).finrank_quotient_add_finrank

theorem all_zero_of_totalDimension_zero [Fintype I]
    (M : LinearSystem.{u,v,w} k I) [∀ i, FiniteDimensional k (M.Value i)]
    (h : M.totalDimension = 0) : ∀ i, ∀ x : M.Value i, x = 0 := by
  intro i x
  have hi : Module.finrank k (M.Value i) = 0 := by
    exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  haveI : Subsingleton (M.Value i) := (Module.finrank_zero_iff.mp hi)
  exact Subsingleton.elim x 0

theorem sub_totalDimension_pos [Fintype I]
    (M : LinearSystem.{u,v,w} k I) [∀ i, FiniteDimensional k (M.Value i)]
    (N : M.Subsystem) (nonzero : ¬ ∀ i, N.obj i = ⊥) :
    0 < (M.subSystem N).totalDimension := by
  by_contra h
  have hz := (M.subSystem N).all_zero_of_totalDimension_zero (by omega)
  apply nonzero
  intro i
  apply le_antisymm
  · intro x hx
    have he := congrArg Subtype.val (hz i ⟨x, hx⟩)
    exact he
  · exact bot_le

theorem quotient_totalDimension_pos [Fintype I]
    (M : LinearSystem.{u,v,w} k I) [∀ i, FiniteDimensional k (M.Value i)]
    (N : M.Subsystem) (proper : ¬ ∀ i, N.obj i = ⊤) :
    0 < (M.quotientSystem N).totalDimension := by
  by_contra h
  have hz := (M.quotientSystem N).all_zero_of_totalDimension_zero (by omega)
  apply proper
  intro i
  apply top_unique
  intro x _
  have he := hz i ((N.obj i).mkQ x)
  exact (Submodule.Quotient.mk_eq_zero (N.obj i)).mp he

/-- Finite-dimensional propagation from simple systems, with all subobject
and quotient dimension-decrease arguments proved. -/
theorem finite_dimensional_reduction [Fintype I]
    (P : LinearSystem.{u,v,w} k I → Prop)
    (zero : ∀ M [∀ i, FiniteDimensional k (M.Value i)],
      (∀ i, ∀ x : M.Value i, x = 0) → P M)
    (simple : ∀ M [∀ i, FiniteDimensional k (M.Value i)], M.IsSimple → P M)
    (extension : ∀ M [∀ i, FiniteDimensional k (M.Value i)] (N : M.Subsystem),
      P (M.subSystem N) → P (M.quotientSystem N) → P M)
    (M : LinearSystem.{u,v,w} k I) [∀ i, FiniteDimensional k (M.Value i)] : P M := by
  classical
  have aux : ∀ n, ∀ (A : LinearSystem.{u,v,w} k I)
      [∀ i, FiniteDimensional k (A.Value i)], A.totalDimension = n → P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ hdim
      by_cases hz : ∀ i, ∀ x : A.Value i, x = 0
      · exact zero A hz
      by_cases hs : A.IsSimple
      · exact simple A hs
      have hnz : ∃ i, ∃ x : A.Value i, x ≠ 0 := by
        push Not at hz
        exact hz
      have hn : ¬ ∀ N : A.Subsystem,
          (∀ i, N.obj i = ⊥) ∨ (∀ i, N.obj i = ⊤) := by
        intro h
        exact hs ⟨hnz, h⟩
      push Not at hn
      obtain ⟨N, hnonzero, hproper⟩ := hn
      have hd := A.totalDimension_sub_add_quotient N
      have hp := A.sub_totalDimension_pos N (not_forall.mpr hnonzero)
      have hq := A.quotient_totalDimension_pos N (not_forall.mpr hproper)
      apply extension A N
      · exact ih (A.subSystem N).totalDimension (by omega) (A.subSystem N) rfl
      · exact ih (A.quotientSystem N).totalDimension (by omega) (A.quotientSystem N) rfl
  exact aux M.totalDimension M rfl

end Sharpness.LinearSystem
