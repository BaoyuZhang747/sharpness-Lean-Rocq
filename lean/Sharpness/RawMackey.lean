import Sharpness.DoubleCosetTwist

/-! The full Mackey formula for arbitrary raw fusion representatives,
deduced from the existing orbit-category formula by actual double-coset
bijections and the proved representative-independence of span operators. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    {R : Type u} [Ring R] (M : MackeyModule.{u,u,w} R F.Orbit F.mackeyShape)

theorem rawDoubleCosetSum_twist (r s : T.subgroup) :
    (∑ i : F.RawDoubleCosetTerm (F.twistLeft f r) (F.twistRight g s),
      F.rawDoubleCosetOperator (F.twistLeft f r) (F.twistRight g s) M i) =
    ∑ i : F.RawDoubleCosetTerm f g, F.rawDoubleCosetOperator f g M i := by
  calc
    _ = ∑ i : F.RawDoubleCosetTerm f g,
        F.rawDoubleCosetOperator (F.twistLeft f r) (F.twistRight g s) M
          (F.rawDoubleCosetTwistEquiv f g r s i) :=
      ((F.rawDoubleCosetTwistEquiv f g r s).sum_comp _).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => F.rawDoubleCosetOperator_twist f g r s M i)

theorem mackey_canonical_raw :
    (M.pull (F.toOrbit.map f)).comp (M.push (F.toOrbit.map g)) =
      ∑ i : F.RawDoubleCosetTerm (F.orbitRepresentative (F.toOrbit.map f))
          (F.orbitRepresentative (F.toOrbit.map g)),
        F.rawDoubleCosetOperator (F.orbitRepresentative (F.toOrbit.map f))
          (F.orbitRepresentative (F.toOrbit.map g)) M i := by
  have h := M.mackey (F.toOrbit.map f) (F.toOrbit.map g)
  change (M.pull (F.toOrbit.map f)).comp (M.push (F.toOrbit.map g)) =
    ∑ i : F.RawDoubleCosetTerm (F.orbitRepresentative (F.toOrbit.map f))
        (F.orbitRepresentative (F.toOrbit.map g)),
      F.rawSpanOperator (F.orbitRepresentative (F.toOrbit.map f))
        (F.orbitRepresentative (F.toOrbit.map g)) M i.out at h
  exact h.trans (Finset.sum_congr rfl (fun i _ =>
    (F.rawDoubleCosetOperator_out _ _ M i).symm))

theorem mackey_raw : (M.pull (F.toOrbit.map f)).comp (M.push (F.toOrbit.map g)) =
    ∑ i : F.RawDoubleCosetTerm f g, F.rawDoubleCosetOperator f g M i := by
  let f₀ := F.orbitRepresentative (F.toOrbit.map f)
  let g₀ := F.orbitRepresentative (F.toOrbit.map g)
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f₀ f).mp (F.orbitRepresentative_map _)
  obtain ⟨s, hs⟩ := (F.orbit_map_eq_iff g₀ g).mp (F.orbitRepresentative_map _)
  have hf : F.twistLeft f₀ r = f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact (hr x).symm
  have hg : F.twistRight g₀ s = g := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact (hs x).symm
  have hsum := F.rawDoubleCosetSum_twist f₀ g₀ M r s
  rw [hf, hg] at hsum
  exact (F.mackey_canonical_raw f g M).trans hsum.symm

end Sharpness.FusionSystem
