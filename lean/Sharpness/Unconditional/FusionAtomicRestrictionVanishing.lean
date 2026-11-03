import Sharpness.Unconditional.FusionAtomicSupport
import Sharpness.Unconditional.AtomicSylowVanishing

/-! The actual atomic coefficient restricted to normalizer preimages has
vanishing higher limits whenever the centric source is nonradical. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hnQ : F.FullyNormalized Q) (R : Type u) [CommRing R]

include hnQ in
/-- Nonradicality provides an actual nontrivial normal p-subgroup, so the
proved ordinary orbit-category vanishing applies to this restriction. -/
theorem atomic_restriction_higherLimits_zero
    (nonradical : ¬ F.IsRadical p Q)
    (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (n : ℕ) : IsZero (higherLimit ((F.atomicNormalizerFunctor Q p hS sat hQ).op ⋙ D) n) := by
  classical
  haveI : Finite (Aut (F.toOrbit.obj ⟨Q⟩)) :=
    Finite.of_injective (fun a : Aut (F.toOrbit.obj ⟨Q⟩) => a.hom) (fun _ _ h => Iso.ext h)
  rw [IsRadical, HasTrivialNormalPSubgroups] at nonradical
  push Not at nonradical
  obtain ⟨N, hnormal, hp, hne⟩ := nonradical
  letI : N.Normal := hnormal
  let T := F.normalizerToOrbitAut_sylow p hS sat Q hnQ
  exact AtomicGroupOrbit.atomic_higherLimits_zero_sylow R T N hp hne
    ((F.atomicNormalizerFunctor Q p hS sat hQ).op ⋙ D)
    (F.atomic_restriction_supported Q p hS sat hQ R D supported) n

end Sharpness.FusionSystem
