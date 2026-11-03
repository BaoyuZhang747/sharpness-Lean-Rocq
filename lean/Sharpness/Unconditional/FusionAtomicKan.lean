import Sharpness.Unconditional.FusionAtomicTerminals
import Sharpness.Unconditional.CommaKanExactTerminal

/-! Exact right Kan extension for the actual atomic normalizer functor.
The indexing factors are the automorphism orbits of fusion arrows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hnQ : F.FullyNormalized Q) (R : Type u) [CommRing R]

include hnQ

/-- Each actual fusion-comma component has a terminal representative, so
the atomic right Kan extension preserves epimorphisms. -/
theorem atomicRan_preservesEpimorphisms :
    ((F.atomicNormalizerFunctor Q p hS sat hQ).op.ran
      (H := ModuleCat.{u} R)).PreservesEpimorphisms :=
  ran_op_preservesEpimorphisms_of_unique_terminal_family
    (F.atomicNormalizerFunctor Q p hS sat hQ) R (F.AtomicMorphismOrbits Q)
    (F.atomicComponentTerminal Q p hS sat hQ hnQ)
    (fun _ X => F.atomicComponentTerminalFamilyUnique Q p hS sat hQ hnQ X)

/-- Exactness of right Kan extension in the form used by derived functors. -/
theorem atomicRan_preservesHomology :
    ((F.atomicNormalizerFunctor Q p hS sat hQ).op.ran
      (H := ModuleCat.{u} R)).PreservesHomology :=
  ran_op_preservesHomology_of_unique_terminal_family
    (F.atomicNormalizerFunctor Q p hS sat hQ) R (F.AtomicMorphismOrbits Q)
    (F.atomicComponentTerminal Q p hS sat hQ hnQ)
    (fun _ X => F.atomicComponentTerminalFamilyUnique Q p hS sat hQ hnQ X)

/-- The actual pointwise formula is a product indexed by automorphism
orbits of fusion arrows, evaluated at their stabilizer representatives. -/
def atomicRanObjIsoProduct (D : (F.AtomicNormalizerOrbit Q p)ᵒᵖ ⥤ ModuleCat.{u} R)
    (P : F.CentricOrbit) :
    (((F.atomicNormalizerFunctor Q p hS sat hQ).op.ran.obj D).obj (op P)) ≅
      ∏ᶜ (fun i : F.AtomicMorphismOrbits Q P =>
        D.obj (op (F.atomicComponentTerminal Q p hS sat hQ hnQ P i).left)) := by
  let T := F.atomicComponentTerminal Q p hS sat hQ hnQ P
  letI := oppositeTerminalFamily_initial (F.atomicNormalizerFunctor Q p hS sat hQ) P T
    (fun X => F.atomicComponentTerminalFamilyUnique Q p hS sat hQ hnQ X)
  exact ranObjIsoProduct R (F.atomicNormalizerFunctor Q p hS sat hQ).op (op P)
    (oppositeTerminalFamily (F.atomicNormalizerFunctor Q p hS sat hQ) P T) D

end Sharpness.FusionSystem
