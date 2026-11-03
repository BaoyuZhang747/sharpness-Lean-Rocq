import Sharpness.Unconditional.MinimalSupport
import Mathlib.RepresentationTheory.Irreducible

/-!
The automorphism-module conclusion at minimal support, expressed using
mathlib's actual `IsSimpleModule` for the group algebra. Automorphisms of
the fusion orbit object are the outer fusion automorphisms; the action is
the existing covariant Mackey action, in Lean's left-module convention.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory
open scoped MonoidAlgebra

private theorem isSimpleModule_of_invariant_submodule
    {k G V : Type u} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)
    (hne : ∃ x : V, x ≠ 0)
    (hsimple : ∀ A : Submodule k V,
      (∀ g : G, ∀ x ∈ A, ρ g x ∈ A) → A = ⊥ ∨ A = ⊤) :
    IsSimpleModule k[G] ρ.asModule := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    obtain ⟨x, hx⟩ := hne
    have hxmem : x ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [h]
      trivial
    exact hx hxmem
  · intro A
    rcases hsimple A.toSubmodule (fun g _ hx => A.apply_mem_toSubmodule g hx) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (Q : Subgroup S) (simple : M.IsSimple)
    (nonzero : ∃ x : M.Value (F.toOrbit.obj ⟨Q⟩), x ≠ 0)
    (small_zero : ∀ L : Subgroup S, Nat.card L < Nat.card Q →
      ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0)

include simple nonzero small_zero

/-- At each fusion conjugate of the chosen least-order nonzero subgroup,
the actual group-algebra module of orbit automorphisms is simple. -/
theorem isSimpleModule_of_isConjugate (P : Subgroup S)
    (hP : F.isoSystem.IsConjugate Q P) :
    IsSimpleModule k[Aut (F.toOrbit.obj ⟨P⟩)]
      (Representation.asModule (M.automorphismAction (F.toOrbit.obj ⟨P⟩))) := by
  obtain ⟨hne, hs⟩ := F.simple_automorphismModule_of_isConjugate
    M Q simple nonzero small_zero P hP
  exact isSimpleModule_of_invariant_submodule _ hne hs

/-- At every inclusion-minimal nonzero subgroup, the actual
orbit-automorphism group-algebra module is simple. -/
theorem isSimpleModule_of_isMinimalSupport (P : Subgroup S)
    (hP : F.IsMinimalSupport M P) :
    IsSimpleModule k[Aut (F.toOrbit.obj ⟨P⟩)]
      (Representation.asModule (M.automorphismAction (F.toOrbit.obj ⟨P⟩))) :=
  F.isSimpleModule_of_isConjugate M Q simple nonzero small_zero P
    (F.isConjugate_of_isMinimalSupport M Q simple nonzero small_zero P hP)

omit simple nonzero small_zero in
/-- Simplicity at a minimal subgroup follows from simplicity of the full
Mackey functor alone: the least-order subgroup is constructed internally. -/
theorem isSimpleModule_at_minimalSupport (hsimple : M.IsSimple)
    (P : Subgroup S) (hP : F.IsMinimalSupport M P) :
    IsSimpleModule k[Aut (F.toOrbit.obj ⟨P⟩)]
      (Representation.asModule (M.automorphismAction (F.toOrbit.obj ⟨P⟩))) := by
  obtain ⟨Q, hQ, hsmall⟩ := F.exists_least_nonzero_support M hsimple
  exact F.isSimpleModule_of_isMinimalSupport M Q hsimple hQ hsmall P hP

omit simple nonzero small_zero in
/-- The complete minimal-support statement: every simple full Mackey
functor has a least-order nonzero subgroup whose fusion class is exactly
the set of minimal subgroups, and all its values are simple modules over
the corresponding outer-automorphism group algebras. -/
theorem minimalSupport_and_simpleModules (hsimple : M.IsSimple) :
    ∃ Q : Subgroup S,
      (∃ x : M.Value (F.toOrbit.obj ⟨Q⟩), x ≠ 0) ∧
      (∀ L : Subgroup S, Nat.card L < Nat.card Q →
        ∀ x : M.Value (F.toOrbit.obj ⟨L⟩), x = 0) ∧
      {P : Subgroup S | F.IsMinimalSupport M P} =
        {P : Subgroup S | F.isoSystem.IsConjugate Q P} ∧
      ∀ P : Subgroup S, F.isoSystem.IsConjugate Q P →
        IsSimpleModule k[Aut (F.toOrbit.obj ⟨P⟩)]
          (Representation.asModule (M.automorphismAction (F.toOrbit.obj ⟨P⟩))) := by
  obtain ⟨Q, hQ, hsmall⟩ := F.exists_least_nonzero_support M hsimple
  exact ⟨Q, hQ, hsmall, F.minimalSupport_eq_fusionClass M Q hsimple hQ hsmall,
    F.isSimpleModule_of_isConjugate M Q hsimple hQ hsmall⟩

end FusionSystem
end Sharpness
