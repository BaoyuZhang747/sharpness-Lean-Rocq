import Sharpness.Unconditional.FusionAtomicFunctor
import Sharpness.Unconditional.AtomicGroupOrbitSylowFusion
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-! Orbit representatives for the comma category of the normalizer-preimage
functor. Stabilizers can be moved into the chosen normalizer Sylow subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hnQ : F.FullyNormalized Q)

local instance atomicMorphismAction (P : F.CentricOrbit) :
    MulAction (Aut (F.toOrbit.obj ⟨Q⟩)) (F.toOrbit.obj ⟨Q⟩ ⟶ P.obj) :=
  F.orbitHomAction _ _

abbrev AtomicMorphismOrbits (P : F.CentricOrbit) :=
  MulAction.orbitRel.Quotient (Aut (F.toOrbit.obj ⟨Q⟩))
    (F.toOrbit.obj ⟨Q⟩ ⟶ P.obj)

include p hS sat hnQ in
theorem exists_atomicComponentRepresentative (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) :
    ∃ f : F.toOrbit.obj ⟨Q⟩ ⟶ P.obj,
      Quotient.mk'' f = i ∧ F.orbitHomStabilizer f ≤ (F.normalizerToOrbitAut Q).range := by
  haveI : Finite (Aut (F.toOrbit.obj ⟨Q⟩)) :=
    Finite.of_injective (fun a : Aut (F.toOrbit.obj ⟨Q⟩) => a.hom) (fun a b h => Iso.ext h)
  let A : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩)) :=
    ⟨F.orbitHomStabilizer i.out, F.orbitHomStabilizer_isPGroup p hS i.out⟩
  obtain ⟨g, hg⟩ := AtomicGroupOrbit.exists_conjugate_le_sylow
    (F.normalizerToOrbitAut_sylow p hS sat Q hnQ) A
  refine ⟨g • i.out, ?_, ?_⟩
  · exact (Quotient.sound (show MulAction.orbitRel _ _ (g • i.out) i.out from
      ⟨g, rfl⟩)).trans (Quotient.out_eq i)
  · rw [← F.orbitHomAction_stabilizer _ _ (g • i.out),
      MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      F.orbitHomAction_stabilizer]
    exact hg

def atomicComponentRepresentative (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) : F.toOrbit.obj ⟨Q⟩ ⟶ P.obj :=
  (F.exists_atomicComponentRepresentative Q p hS sat hnQ P i).choose

theorem atomicComponentRepresentative_class (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) :
    Quotient.mk'' (F.atomicComponentRepresentative Q p hS sat hnQ P i) = i :=
  (F.exists_atomicComponentRepresentative Q p hS sat hnQ P i).choose_spec.1

theorem atomicComponentRepresentative_stabilizer_le (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) :
    F.orbitHomStabilizer (F.atomicComponentRepresentative Q p hS sat hnQ P i) ≤
      (F.normalizerToOrbitAut Q).range :=
  (F.exists_atomicComponentRepresentative Q p hS sat hnQ P i).choose_spec.2

abbrev AtomicComma (P : F.CentricOrbit) :=
  CostructuredArrow (F.atomicNormalizerFunctor Q p hS sat hQ) P

def atomicCommaRestriction {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) : F.toOrbit.obj ⟨Q⟩ ⟶ P.obj :=
  F.atomicPreimageInclusion Q X.left.obj.as.subgroup ≫ X.hom.hom

theorem atomicCommaRestriction_fixed {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) :
    X.left.obj.as.subgroup ≤ F.orbitHomStabilizer (F.atomicCommaRestriction Q p hS sat hQ X) :=
  F.atomicNormalizerPreimage_restriction_fixed Q X.left.obj.as.subgroup X.left.property X.hom.hom

theorem atomicCommaRestriction_map {P : F.CentricOrbit}
    {X Y : F.AtomicComma Q p hS sat hQ P} (f : X ⟶ Y) :
    F.atomicCommaRestriction Q p hS sat hQ X =
      (F.atomicOrbitRepresentative Q p f.left.hom).val.inv ≫
        F.atomicCommaRestriction Q p hS sat hQ Y := by
  have hw := congrArg (fun z => z.hom) (CostructuredArrow.w f)
  change ((F.atomicNormalizerFunctor Q p hS sat hQ).map f.left).hom ≫ Y.hom.hom =
    X.hom.hom at hw
  change F.atomicPreimageInclusion Q X.left.obj.as.subgroup ≫ X.hom.hom = _
  rw [← hw, ← Category.assoc, F.atomicNormalizerFunctor_map_spec, Category.assoc]
  rfl

def atomicCommaComponent {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) : F.AtomicMorphismOrbits Q P :=
  Quotient.mk'' (F.atomicCommaRestriction Q p hS sat hQ X)

theorem atomicCommaComponent_map {P : F.CentricOrbit}
    {X Y : F.AtomicComma Q p hS sat hQ P} (f : X ⟶ Y) :
    F.atomicCommaComponent Q p hS sat hQ X = F.atomicCommaComponent Q p hS sat hQ Y := by
  apply Quotient.sound
  refine ⟨(F.atomicOrbitRepresentative Q p f.left.hom).val, ?_⟩
  exact (F.atomicCommaRestriction_map Q p hS sat hQ f).symm

def atomicComponentObject (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) : F.AtomicNormalizerOrbit Q p :=
  ⟨AtomicGroupOrbit.toOrbit.obj
      ⟨F.orbitHomStabilizer (F.atomicComponentRepresentative Q p hS sat hnQ P i),
        F.orbitHomStabilizer_isPGroup p hS _⟩,
    F.atomicComponentRepresentative_stabilizer_le Q p hS sat hnQ P i⟩

def atomicComponentTerminal (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) : F.AtomicComma Q p hS sat hQ P :=
  CostructuredArrow.mk (Y := F.atomicComponentObject Q p hS sat hnQ P i)
    (ObjectProperty.homMk
      ((F.atomicFixedRestrictionEquiv Q
        (F.orbitHomStabilizer (F.atomicComponentRepresentative Q p hS sat hnQ P i))
        p hS sat hQ
        (F.atomicComponentRepresentative_stabilizer_le Q p hS sat hnQ P i) P.obj).symm
        ⟨F.atomicComponentRepresentative Q p hS sat hnQ P i, le_rfl⟩))

theorem atomicComponentTerminal_restriction (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) :
    F.atomicCommaRestriction Q p hS sat hQ
        (F.atomicComponentTerminal Q p hS sat hQ hnQ P i) =
      F.atomicComponentRepresentative Q p hS sat hnQ P i :=
  congrArg Subtype.val ((F.atomicFixedRestrictionEquiv Q _ p hS sat hQ
    (F.atomicComponentRepresentative_stabilizer_le Q p hS sat hnQ P i) P.obj).apply_symm_apply _)

theorem atomicComponentTerminal_component (P : F.CentricOrbit)
    (i : F.AtomicMorphismOrbits Q P) :
    F.atomicCommaComponent Q p hS sat hQ
        (F.atomicComponentTerminal Q p hS sat hQ hnQ P i) = i := by
  change Quotient.mk'' (F.atomicCommaRestriction Q p hS sat hQ _) = i
  rw [F.atomicComponentTerminal_restriction]
  exact F.atomicComponentRepresentative_class Q p hS sat hnQ P i

end Sharpness.FusionSystem
