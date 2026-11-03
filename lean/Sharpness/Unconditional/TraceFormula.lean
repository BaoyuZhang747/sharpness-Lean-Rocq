import Sharpness.CentralizerZero
import Sharpness.RawMackey

/-! Reduction of the minimal-simple restriction formula to concrete double
cosets.  Everything here is proved from the full Mackey formula and the
minimality data of `SimpleLabel`; no published trace formula is assumed. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M)

/-- To bound the image of a restriction out of a simple functor, it suffices
to bound its composites with transfers from its minimal subgroup class. -/
theorem restriction_range_le_of_minimal_transfers
    {T P : F.Orbit} (f : P ⟶ T) (A : Submodule k (M.Value P))
    (h : ∀ L : F.MinimalInclusionIndex label.Q T,
      LinearMap.range ((M.pull f).comp (M.push (F.minimalInclusion L))) ≤ A) :
    LinearMap.range (M.pull f) ≤ A := by
  have hgen := F.simple_inclusion_generation M label.Q label.small_zero
    label.simple label.nonzero T
  have hle : (⨆ L : F.MinimalInclusionIndex label.Q T,
      LinearMap.range (M.push (F.minimalInclusion L))) ≤ A.comap (M.pull f) := by
    refine iSup_le fun L x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact h L ⟨y, rfl⟩
  rw [hgen] at hle
  rintro x ⟨y, rfl⟩
  exact hle (Submodule.mem_top)

/-- Terms through a proper subgroup of the minimal class vanish separately. -/
theorem rawSpanOperator_eq_zero_of_small
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (t : T.subgroup)
    (small : F.orbitOrder (F.toOrbit.obj (F.spanApex f g t)) <
      F.orbitOrder label.Q) :
    F.rawSpanOperator f g M t = 0 := by
  ext x
  change M.push (F.toOrbit.map (F.spanLeft f g t))
    (M.pull (F.toOrbit.map (F.concreteSpan f g t).right) x) = 0
  have hz := label.small_zero (F.toOrbit.obj (F.spanApex f g t)) small
    (M.pull (F.toOrbit.map (F.concreteSpan f g t).right) x)
  exact (congrArg (M.push (F.toOrbit.map (F.spanLeft f g t))) hz).trans (map_zero _)

/-- The Mackey formula with all proper-apex summands removed. This finite
sum is the remaining group-theoretic expression to identify with a trace. -/
theorem minimal_mackey_raw
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (hP : F.orbitOrder (F.toOrbit.obj P) = F.orbitOrder label.Q) :
    (M.pull (F.toOrbit.map f)).comp (M.push (F.toOrbit.map g)) =
      ∑ i : F.RawDoubleCosetTerm f g,
        if F.orbitOrder (F.toOrbit.obj (F.spanApex f g i.out)) =
            F.orbitOrder label.Q then F.rawDoubleCosetOperator f g M i else 0 := by
  classical
  rw [F.mackey_raw f g M]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · rw [F.rawDoubleCosetOperator_out f g M i]
    apply F.rawSpanOperator_eq_zero_of_small M label f g i.out
    exact lt_of_le_of_ne
      ((F.orbitOrder_mono (F.toOrbit.map (F.spanLeft f g i.out))).trans_eq hP) hi

/-- If none of the intersection spans has full minimal order, the whole
restriction-transfer composite vanishes. -/
theorem minimal_mackey_raw_eq_zero
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (hP : F.orbitOrder (F.toOrbit.obj P) = F.orbitOrder label.Q)
    (proper : ∀ t : T.subgroup,
      F.orbitOrder (F.toOrbit.obj (F.spanApex f g t)) ≠ F.orbitOrder label.Q) :
    (M.pull (F.toOrbit.map f)).comp (M.push (F.toOrbit.map g)) = 0 := by
  classical
  rw [F.minimal_mackey_raw M label f g hP]
  exact Finset.sum_eq_zero (fun i _ => if_neg (proper i.out))

end Sharpness.FusionSystem
