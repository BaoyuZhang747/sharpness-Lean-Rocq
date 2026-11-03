import Sharpness.Unconditional.FusionAtomicRestrictionVanishing
import Sharpness.Unconditional.FusionAtomicReconstruction

/-! Unconditional atomic vanishing on the centric fusion orbit category.
The proof combines actual fixed-point Kan comparison with the normal
p-subgroup reflector, then transports the label to a fully normalized
fusion conjugate. No published proposition remains a hypothesis. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (R : Type u) [CommRing R]

include hS sat

/-- Atomic vanishing for a fully normalized, centric, nonradical label. -/
theorem nonradical_atomic_higherLimits_zero_fullyNormalized
    (Q : Subgroup S) (hQ : F.IsCentric Q) (hnQ : F.FullyNormalized Q)
    (nonradical : ¬ F.IsRadical p Q)
    (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (n : ℕ) : IsZero (higherLimit D n) :=
  IsZero.of_iso
    (F.atomic_restriction_higherLimits_zero Q p hS sat hQ hnQ R nonradical D supported n)
    (F.atomicHigherLimitIso Q p hS sat hQ hnQ R D supported n).symm

/-- Every atomic coefficient at a nonradical centric isomorphism class
has zero higher limits in all degrees, over any commutative ring. -/
theorem nonradical_atomic_higherLimits_zero
    (Q : F.CentricOrbit) (nonradical : ¬ F.IsRadical p Q.obj.as.subgroup)
    (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ Q) → IsZero (D.obj (op P)))
    (n : ℕ) : IsZero (higherLimit D n) := by
  obtain ⟨T, e, he, hnT⟩ := F.exists_fullyNormalized Q.obj.as.subgroup
  have hT : F.IsCentric T := F.isoSystem.centricIn_of_iso e he Q.property
  let e₀ := F.toOrbit.mapIso (F.isoOfMulEquiv e he)
  let eC : Q ≅ F.atomicSource T hT := ObjectProperty.isoMk _ e₀
  apply F.nonradical_atomic_higherLimits_zero_fullyNormalized p hS sat R T hT hnT
  · intro hrad
    exact nonradical (F.radical_of_orbitIso e₀.symm hrad)
  · intro P hP
    apply supported P
    rintro ⟨a⟩
    exact hP ⟨a.trans eC⟩

end Sharpness.FusionSystem
