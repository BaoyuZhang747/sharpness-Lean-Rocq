import Sharpness.StableFunctors
import Sharpness.GroupCohomologyMackey

/-! Stability on all orbit arrows is exactly the manuscript's
condition comparing every map to the top subgroup with inclusion.
For ordinary cohomology the condition uses actual raw fusion maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)

theorem mem_stableElements_iff_toTop
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) (x : M.Value F.topOrbit) :
    x ∈ F.stableElements M ↔ ∀ (P : F.Orbit) (f : P ⟶ F.topOrbit),
      M.pull f x = M.pull (F.toTop P) x := by
  constructor
  · intro hx P f
    have h : M.pull f (M.pull (F.toTop F.topOrbit) x) = M.pull (F.toTop P) x := hx f
    simpa only [F.toTop_top, M.pull_id, LinearMap.id_apply] using h
  · intro hx P Q f
    exact (LinearMap.congr_fun (M.pull_comp f (F.toTop Q)) x).symm.trans
      (hx P (f ≫ F.toTop Q))

variable {A : Type u} [AddCommGroup A] [Module R A] {n : ℕ}
    (I : F.GroupCohomologyTransferLaws (R := R) A n)

theorem mem_ordinaryStableElements_iff_raw_toTop
    (x : (F.groupCohomologyMackey I).Value F.topOrbit) :
    x ∈ F.stableElements (F.groupCohomologyMackey I) ↔
      ∀ (P : F.Object) (f : P ⟶ (⟨⊤⟩ : F.Object)),
        OrdinaryCohomology.pullLinear (R := R) (A := A) f.val n x =
          OrdinaryCohomology.pullLinear (R := R) (A := A)
            (F.inclusion (show P.subgroup ≤ ⊤ from le_top)).val n x := by
  rw [F.mem_stableElements_iff_toTop]
  constructor
  · intro hx P f
    have h := hx (F.toOrbit.obj P) (F.toOrbit.map f)
    calc
      _ = (F.groupCohomologyMackey I).pull (F.toOrbit.map f) x :=
        (LinearMap.congr_fun (F.groupCohomologyMackey_pull_raw I f) x).symm
      _ = (F.groupCohomologyMackey I).pull (F.toTop (F.toOrbit.obj P)) x := h
      _ = _ := LinearMap.congr_fun
        (F.groupCohomologyMackey_pull_raw I (F.inclusion (show P.subgroup ≤ ⊤ from le_top))) x
  · intro hx P f
    have hf := F.groupCohomologyMackey_pull_raw I (F.orbitRepresentative f)
    rw [F.orbitRepresentative_map f] at hf
    calc
      _ = OrdinaryCohomology.pullLinear (R := R) (A := A) (F.orbitRepresentative f).val n x :=
        LinearMap.congr_fun hf x
      _ = OrdinaryCohomology.pullLinear (R := R) (A := A)
          (F.inclusion (show P.as.subgroup ≤ ⊤ from le_top)).val n x :=
        hx P.as (F.orbitRepresentative f)
      _ = _ := (LinearMap.congr_fun
        (F.groupCohomologyMackey_pull_raw I (F.inclusion (show P.as.subgroup ≤ ⊤ from le_top))) x).symm

end Sharpness.FusionSystem
