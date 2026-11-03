import Sharpness.Unconditional.FusionAtomicExtension
import Sharpness.Unconditional.CentricRigidity

/-! The fixed-point representability statement in BLO Proposition 3.2,
proved from saturation and centric rigidity on actual orbit morphisms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (H : Subgroup (Aut (F.toOrbit.obj ⟨Q⟩)))

abbrev AtomicFixedMorphisms (P : F.Orbit) :=
  {f : F.toOrbit.obj ⟨Q⟩ ⟶ P // H ≤ F.orbitHomStabilizer f}

def atomicFixedRestriction (hH : H ≤ (F.normalizerToOrbitAut Q).range)
    (P : F.Orbit) :
    (F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q H⟩ ⟶ P) → F.AtomicFixedMorphisms Q H P :=
  fun f => ⟨F.toOrbit.map (F.inclusion (F.le_atomicNormalizerPreimage Q H)) ≫ f,
    F.atomicNormalizerPreimage_restriction_fixed Q H hH f⟩

theorem atomicFixedRestriction_injective (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) (P : F.Orbit) :
    Function.Injective (F.atomicFixedRestriction Q H hH P) := by
  intro f g hfg
  obtain ⟨f, rfl⟩ := F.toOrbit.map_surjective f
  obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective g
  have hh := congrArg Subtype.val hfg
  change F.toOrbit.map (F.inclusion (F.le_atomicNormalizerPreimage Q H)) ≫ F.toOrbit.map f =
    F.toOrbit.map (F.inclusion (F.le_atomicNormalizerPreimage Q H)) ≫ F.toOrbit.map g at hh
  rw [← F.toOrbit.map_comp, ← F.toOrbit.map_comp] at hh
  exact F.centric_normal_orbit_restriction_injective p hS sat
    (F.le_atomicNormalizerPreimage Q H) hQ f g hh

theorem atomicFixedRestriction_surjective (p : ℕ)
    (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) (P : F.Orbit) :
    Function.Surjective (F.atomicFixedRestriction Q H hH P) := by
  intro f
  let f₀ := F.orbitRepresentative f.val
  have hw : ∀ n : F.atomicNormalizerPreimage Q H, ∃ r : P.as.subgroup, ∀ x : Q,
      (f₀.val (Q.normalizerMonoidHom
        ⟨n.val, F.atomicNormalizerPreimage_le_normalizer Q H n.property⟩ x)).val =
      r.val * (f₀.val x).val * r.val⁻¹ := by
    intro n
    obtain ⟨hn, ha⟩ := (F.mem_atomicNormalizerPreimage Q H n.val).mp n.property
    apply F.fixed_normalizer_has_target_witness f₀ ⟨n.val, hn⟩
    rw [F.orbitRepresentative_map]
    exact f.property ha
  obtain ⟨g, hg, hext⟩ := F.centric_normalizer_extension p sat
    (F.le_atomicNormalizerPreimage Q H) (F.atomicNormalizerPreimage_le_normalizer Q H)
    hQ f₀ hw
  refine ⟨F.toOrbit.map ⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  change F.toOrbit.map (F.inclusion _) ≫ F.toOrbit.map _ = f.val
  rw [← F.toOrbit.map_comp]
  have hraw : F.inclusion (F.le_atomicNormalizerPreimage Q H) ≫
      (⟨g, hg⟩ : (⟨F.atomicNormalizerPreimage Q H⟩ : F.Object) ⟶ P.as) = f₀ := by
    apply Subtype.ext
    ext x
    exact hext x
  rw [hraw]
  exact F.orbitRepresentative_map f.val

/-- Restriction identifies morphisms out of the normalizer preimage with
the fixed points of the prescribed outer-automorphism subgroup. -/
def atomicFixedRestrictionEquiv (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) (P : F.Orbit) :
    (F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q H⟩ ⟶ P) ≃ F.AtomicFixedMorphisms Q H P :=
  Equiv.ofBijective (F.atomicFixedRestriction Q H hH P)
    ⟨F.atomicFixedRestriction_injective Q H p hS sat hQ hH P,
      F.atomicFixedRestriction_surjective Q H p sat hQ hH P⟩

def atomicFixedPostcomp {P P' : F.Orbit} (g : P ⟶ P') :
    F.AtomicFixedMorphisms Q H P → F.AtomicFixedMorphisms Q H P' :=
  fun f => ⟨f.val ≫ g, by
    intro a ha
    change a.hom ≫ (f.val ≫ g) = f.val ≫ g
    rw [← Category.assoc, f.property ha]⟩

theorem atomicFixedRestriction_naturality
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) {P P' : F.Orbit} (g : P ⟶ P')
    (f : F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q H⟩ ⟶ P) :
    F.atomicFixedRestriction Q H hH P' (f ≫ g) =
      F.atomicFixedPostcomp Q H g (F.atomicFixedRestriction Q H hH P f) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

end Sharpness.FusionSystem
