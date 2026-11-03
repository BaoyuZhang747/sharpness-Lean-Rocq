import Sharpness.Unconditional.FusionAtomicKan
import Sharpness.Unconditional.FusionAtomicSupport
import Sharpness.Unconditional.AtomicKanUnit
import Sharpness.Unconditional.LinearAdjunction
import Sharpness.Unconditional.ProjectiveCoefficients
import Sharpness.HigherLimitFunctor

/-! An atomic coefficient is recovered by the exact right Kan extension
of its restriction to normalizer preimages. Derived adjunction therefore
identifies its actual higher limits with ordinary group-orbit higher limits. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hnQ : F.FullyNormalized Q) (R : Type u) [CommRing R]

local instance atomicReconstructionAction (P : F.CentricOrbit) :
    MulAction (Aut (F.toOrbit.obj ⟨Q⟩)) (F.toOrbit.obj ⟨Q⟩ ⟶ P.obj) :=
  F.orbitHomAction _ _

include hnQ in
theorem atomicRan_zero_off_support (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (P : F.CentricOrbit) (hne : ¬ Nonempty (P ≅ F.atomicSource Q hQ)) :
    IsZero ((((F.atomicNormalizerFunctor Q p hS sat hQ).op.ran.obj
      ((F.atomicNormalizerFunctor Q p hS sat hQ).op ⋙ D)).obj (op P))) := by
  let α := F.atomicNormalizerFunctor Q p hS sat hQ
  let E := α.op ⋙ D
  let V : F.AtomicMorphismOrbits Q P → ModuleCat.{u} R := fun i =>
    E.obj (op (F.atomicComponentTerminal Q p hS sat hQ hnQ P i).left)
  have hV : IsZero (Discrete.functor V) := by
    apply Functor.isZero
    intro i
    exact F.atomicComponentTerminal_zero_off_support Q p hS sat hQ hnQ R D supported P hne i.as
  exact IsZero.of_iso ((limit.isLimit (Discrete.functor V)).isZero_pt hV)
    (F.atomicRanObjIsoProduct Q p hS sat hQ hnQ R E P)

include hnQ in
theorem atomicRanUnit_isIso (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P))) :
    IsIso (((F.atomicNormalizerFunctor Q p hS sat hQ).op.ranAdjunction
      (ModuleCat.{u} R)).unit.app D) := by
  classical
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  by_cases he : Nonempty (P.unop ≅ F.atomicSource Q hQ)
  · obtain ⟨e⟩ := he
    let i : F.AtomicMorphismOrbits Q P.unop := Quotient.mk'' e.inv.hom
    let T := F.atomicComponentTerminal Q p hS sat hQ hnQ P.unop i
    letI : IsIso T.hom := F.atomicComponentTerminal_hom_isIso Q p hS sat hQ hnQ P.unop e i
    exact ran_op_unit_isIso_app_of_terminal R (F.atomicNormalizerFunctor Q p hS sat hQ)
      D P.unop T (F.atomicComponent_isTerminal Q p hS sat hQ hnQ P.unop e i)
  · exact isIso_of_source_target_iso_zero _ (supported P.unop he).isoZero
      (F.atomicRan_zero_off_support Q p hS sat hQ hnQ R D supported P.unop he).isoZero

/-- Atomic higher-limit comparison, constructed from exact right Kan
extension and the actual projective-resolution Ext adjunction. -/
def atomicHigherLimitIso (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (n : ℕ) :
    higherLimit ((F.atomicNormalizerFunctor Q p hS sat hQ).op ⋙ D) n ≅ higherLimit D n := by
  let α := F.atomicNormalizerFunctor Q p hS sat hQ
  let L := restrictionCoefficientFunctor R α
  let G := α.op.ran (H := ModuleCat.{u} R)
  haveI : L.PreservesHomology := by
    dsimp [L, restrictionCoefficientFunctor]
    infer_instance
  haveI : G.PreservesEpimorphisms := F.atomicRan_preservesEpimorphisms Q p hS sat hQ hnQ R
  haveI : G.IsRightAdjoint := (α.op.ranAdjunction (ModuleCat.{u} R)).isRightAdjoint
  haveI : G.Additive := Functor.additive_of_preserves_binary_products G
  haveI : G.Linear R := rightAdjointLinear R
    (L := L) (G := G) (α.op.ranAdjunction (ModuleCat.{u} R))
  haveI := F.atomicRanUnit_isIso Q p hS sat hQ hnQ R D supported
  exact extAdjunctionIso R (L := L) (G := G)
      (α.op.ranAdjunction (ModuleCat.{u} R)) (constantCoefficient R F.CentricOrbit)
      (α.op ⋙ D) n ≪≫
    higherLimitIso (asIso (((α.op.ranAdjunction (ModuleCat.{u} R)).unit.app D))).symm n

end Sharpness.FusionSystem
