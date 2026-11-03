import Sharpness.Unconditional.FusionAtomicComponents
import Sharpness.Unconditional.AtomicOrbitStabilizer

/-! Every component of the normalizer-preimage comma category has a
terminal object, represented by the stabilizer of a fusion-orbit arrow. -/

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

local instance atomicTerminalAction (P : F.CentricOrbit) :
    MulAction (Aut (F.toOrbit.obj ⟨Q⟩)) (F.toOrbit.obj ⟨Q⟩ ⟶ P.obj) :=
  F.orbitHomAction _ _

def atomicComponentHomEquiv (P : F.CentricOrbit) (i : F.AtomicMorphismOrbits Q P)
    (A : F.AtomicNormalizerOrbit Q p) :
    (A ⟶ F.atomicComponentObject Q p hS sat hnQ P i) ≃
      AtomicGroupOrbit.FixedOrbit A.obj.as (F.atomicComponentRepresentative Q p hS sat hnQ P i) := by
  let e := AtomicGroupOrbit.orbitHomToStabilizerEquivOfEq A.obj.as
    (F.atomicComponentObject Q p hS sat hnQ P i).obj.as
    (F.atomicComponentRepresentative Q p hS sat hnQ P i)
    (F.orbitHomAction_stabilizer _ _ _).symm
  exact
    { toFun := fun f => e f.hom
      invFun := fun y => ObjectProperty.homMk (e.symm y)
      left_inv := fun f => by
        apply ObjectProperty.hom_ext
        exact e.symm_apply_apply f.hom
      right_inv := fun y => e.apply_symm_apply y }

theorem atomicComponentHomEquiv_val (P : F.CentricOrbit) (i : F.AtomicMorphismOrbits Q P)
    (A : F.AtomicNormalizerOrbit Q p)
    (f : A ⟶ F.atomicComponentObject Q p hS sat hnQ P i) :
    (F.atomicComponentHomEquiv Q p hS sat hnQ P i A f).val =
      (F.atomicOrbitRepresentative Q p f.hom).val.inv ≫
        F.atomicComponentRepresentative Q p hS sat hnQ P i := by
  change (AtomicGroupOrbit.orbitHomToStabilizerEquivOfEq A.obj.as _ _ _ f.hom).val = _
  nth_rw 1 [← F.atomicOrbitRepresentative_map Q p f.hom]
  exact AtomicGroupOrbit.orbitHomToStabilizerEquivOfEq_map A.obj.as
    (F.atomicComponentObject Q p hS sat hnQ P i).obj.as
    (F.atomicComponentRepresentative Q p hS sat hnQ P i)
    (F.orbitHomAction_stabilizer _ _ _).symm (F.atomicOrbitRepresentative Q p f.hom)

def atomicComponentLift {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) (i : F.AtomicMorphismOrbits Q P)
    (hi : F.atomicCommaComponent Q p hS sat hQ X = i) :
    X ⟶ F.atomicComponentTerminal Q p hS sat hQ hnQ P i := by
  let y : AtomicGroupOrbit.FixedOrbit X.left.obj.as
      (F.atomicComponentRepresentative Q p hS sat hnQ P i) :=
    ⟨F.atomicCommaRestriction Q p hS sat hQ X, by
      rw [F.orbitHomAction_stabilizer]
      exact F.atomicCommaRestriction_fixed Q p hS sat hQ X,
      Quotient.exact (hi.trans (F.atomicComponentRepresentative_class Q p hS sat hnQ P i).symm)⟩
  let f := (F.atomicComponentHomEquiv Q p hS sat hnQ P i X.left).symm y
  refine CostructuredArrow.homMk f ?_
  apply ObjectProperty.hom_ext
  apply F.atomicFixedRestriction_injective Q X.left.obj.as.subgroup p hS sat hQ
    X.left.property P.obj
  apply Subtype.ext
  change F.atomicPreimageInclusion Q X.left.obj.as.subgroup ≫
    (((F.atomicNormalizerFunctor Q p hS sat hQ).map f).hom ≫ _) =
      F.atomicCommaRestriction Q p hS sat hQ X
  rw [← Category.assoc, F.atomicNormalizerFunctor_map_spec, Category.assoc]
  change (F.atomicOrbitRepresentative Q p f.hom).val.inv ≫
    F.atomicCommaRestriction Q p hS sat hQ
      (F.atomicComponentTerminal Q p hS sat hQ hnQ P i) = _
  rw [F.atomicComponentTerminal_restriction, ← F.atomicComponentHomEquiv_val]
  exact congrArg Subtype.val
    ((F.atomicComponentHomEquiv Q p hS sat hnQ P i X.left).apply_symm_apply y)

theorem atomicComponentHom_val_of_comma {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) (i : F.AtomicMorphismOrbits Q P)
    (f : X ⟶ F.atomicComponentTerminal Q p hS sat hQ hnQ P i) :
    (F.atomicComponentHomEquiv Q p hS sat hnQ P i X.left f.left).val =
      F.atomicCommaRestriction Q p hS sat hQ X := by
  rw [F.atomicComponentHomEquiv_val]
  have hf := F.atomicCommaRestriction_map Q p hS sat hQ f
  rw [F.atomicComponentTerminal_restriction] at hf
  exact hf.symm

theorem atomicComponentHom_subsingleton {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) (i : F.AtomicMorphismOrbits Q P) :
    Subsingleton (X ⟶ F.atomicComponentTerminal Q p hS sat hQ hnQ P i) := by
  refine ⟨fun f g => ?_⟩
  apply CostructuredArrow.hom_ext
  apply (F.atomicComponentHomEquiv Q p hS sat hnQ P i X.left).injective
  apply Subtype.ext
  rw [F.atomicComponentHom_val_of_comma, F.atomicComponentHom_val_of_comma]

/-- Every comma object has a unique arrow to exactly one chosen terminal
representative. This is the discrete-final-family input for exact Ran. -/
@[reducible] def atomicComponentTerminalFamilyUnique {P : F.CentricOrbit}
    (X : F.AtomicComma Q p hS sat hQ P) :
    Unique (Σ i : F.AtomicMorphismOrbits Q P,
      X ⟶ F.atomicComponentTerminal Q p hS sat hQ hnQ P i) where
  default := ⟨F.atomicCommaComponent Q p hS sat hQ X,
    F.atomicComponentLift Q p hS sat hQ hnQ X _ rfl⟩
  uniq y := by
    rcases y with ⟨i, f⟩
    have hi : F.atomicCommaComponent Q p hS sat hQ X = i := by
      rw [F.atomicCommaComponent_map Q p hS sat hQ f]
      exact F.atomicComponentTerminal_component Q p hS sat hQ hnQ P i
    subst i
    congr 1
    exact (F.atomicComponentHom_subsingleton Q p hS sat hQ hnQ X _).elim _ _

end Sharpness.FusionSystem
