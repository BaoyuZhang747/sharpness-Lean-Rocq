import Sharpness.Unconditional.FusionAtomicTerminals
import Sharpness.HigherLimits
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! The support computations for atomic comparison: away from the source
isomorphism class, all comma components have nontrivial stabilizer. On
the source isomorphism class there is a single component with an isomorphism
as its terminal arrow. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hnQ : F.FullyNormalized Q)

local instance atomicSupportAction (P : F.CentricOrbit) :
    MulAction (Aut (F.toOrbit.obj ⟨Q⟩)) (F.toOrbit.obj ⟨Q⟩ ⟶ P.obj) :=
  F.orbitHomAction _ _

abbrev atomicSource : F.CentricOrbit := ⟨F.toOrbit.obj ⟨Q⟩, hQ⟩

theorem atomicNormalizerPreimage_eq_bot (hQ : F.IsCentric Q) :
    F.atomicNormalizerPreimage Q ⊥ = Q := by
  apply le_antisymm _ (F.le_atomicNormalizerPreimage Q ⊥)
  intro s hs
  obtain ⟨hn, ha⟩ := (F.mem_atomicNormalizerPreimage Q ⊥ s).mp hs
  have hc : Subgroup.centralizer (Q : Set S) ≤ Q := by
    simpa only [inf_top_eq] using hQ Q le_top (MulEquiv.refl Q) (F.id_mem Q)
  exact (F.relativeNormalizerToAut_eq_one_iff hc
    (⟨s, hn, Subgroup.mem_top _⟩ : F.relativeNormalizer ⊤ Q)).mp ha

theorem atomicNormalizerFunctor_not_iso_of_nontrivial
    (H : F.AtomicNormalizerOrbit Q p) (hH : H.obj.as.subgroup ≠ ⊥) :
    ¬ Nonempty ((F.atomicNormalizerFunctor Q p hS sat hQ).obj H ≅ F.atomicSource Q hQ) := by
  rintro ⟨e⟩
  have he : F.atomicNormalizerPreimage Q H.obj.as.subgroup = Q := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge (F.le_atomicNormalizerPreimage Q H.obj.as.subgroup)
    exact F.orbitOrder_mono e.hom.hom
  exact F.atomicNormalizerPreimage_ne_of_nontrivial Q H.obj.as.subgroup H.property hH he

theorem atomic_restriction_supported (R : Type u) [CommRing R]
    (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (H : F.AtomicNormalizerOrbit Q p) (hH : H.obj.as.subgroup ≠ ⊥) :
    IsZero (((F.atomicNormalizerFunctor Q p hS sat hQ).op ⋙ D).obj (op H)) :=
  supported _ (F.atomicNormalizerFunctor_not_iso_of_nontrivial Q p hS sat hQ H hH)

theorem atomicComponentObject_nontrivial (P : F.CentricOrbit)
    (hne : ¬ Nonempty (P ≅ F.atomicSource Q hQ)) (i : F.AtomicMorphismOrbits Q P) :
    (F.atomicComponentObject Q p hS sat hnQ P i).obj.as.subgroup ≠ ⊥ := by
  apply F.orbitHomStabilizer_ne_bot_of_not_iso p hS _ hQ
  rintro ⟨e⟩
  exact hne ⟨ObjectProperty.isoMk _ e.symm⟩

theorem atomicComponentTerminal_zero_off_support (R : Type u) [CommRing R]
    (D : CoefficientCategory R F.CentricOrbit)
    (supported : ∀ P, ¬ Nonempty (P ≅ F.atomicSource Q hQ) → IsZero (D.obj (op P)))
    (P : F.CentricOrbit) (hne : ¬ Nonempty (P ≅ F.atomicSource Q hQ))
    (i : F.AtomicMorphismOrbits Q P) :
    IsZero (D.obj (op ((F.atomicNormalizerFunctor Q p hS sat hQ).obj
      (F.atomicComponentTerminal Q p hS sat hQ hnQ P i).left))) :=
  F.atomic_restriction_supported Q p hS sat hQ R D supported _
    (F.atomicComponentObject_nontrivial Q p hS sat hQ hnQ P hne i)

theorem atomicMorphism_isIso (P : F.CentricOrbit)
    (e : P ≅ F.atomicSource Q hQ) (f : F.toOrbit.obj ⟨Q⟩ ⟶ P.obj) : IsIso f := by
  apply F.orbit_isIso_of_equal_order
  apply le_antisymm (F.orbitOrder_mono e.inv.hom) (F.orbitOrder_mono e.hom.hom)

theorem atomicMorphismOrbits_subsingleton (P : F.CentricOrbit)
    (e : P ≅ F.atomicSource Q hQ) : Subsingleton (F.AtomicMorphismOrbits Q P) := by
  refine ⟨fun i j => ?_⟩
  induction i using Quotient.inductionOn with
  | h f =>
    induction j using Quotient.inductionOn with
    | h g =>
      letI := F.atomicMorphism_isIso Q hQ P e f
      letI := F.atomicMorphism_isIso Q hQ P e g
      apply Quotient.sound
      refine ⟨(asIso g).trans (asIso f).symm, ?_⟩
      change (f ≫ inv g) ≫ g = f
      simp

def atomicComponent_isTerminal (P : F.CentricOrbit)
    (e : P ≅ F.atomicSource Q hQ) (i : F.AtomicMorphismOrbits Q P) :
    IsTerminal (F.atomicComponentTerminal Q p hS sat hQ hnQ P i) := by
  letI := F.atomicMorphismOrbits_subsingleton Q hQ P e
  exact IsTerminal.ofUniqueHom
    (fun X => F.atomicComponentLift Q p hS sat hQ hnQ X i (Subsingleton.elim _ _))
    (fun X f => (F.atomicComponentHom_subsingleton Q p hS sat hQ hnQ X i).elim _ _)

theorem atomicComponentTerminal_hom_isIso (P : F.CentricOrbit)
    (e : P ≅ F.atomicSource Q hQ) (i : F.AtomicMorphismOrbits Q P) :
    IsIso (F.atomicComponentTerminal Q p hS sat hQ hnQ P i).hom := by
  apply (ObjectProperty.isIso_hom_iff _).mp
  apply F.orbit_isIso_of_equal_order
  apply le_antisymm (F.orbitOrder_mono
    (F.atomicComponentTerminal Q p hS sat hQ hnQ P i).hom.hom)
  exact (F.orbitOrder_mono e.hom.hom).trans
    (F.orbitOrder_mono (F.atomicPreimageInclusion Q _))

end Sharpness.FusionSystem
