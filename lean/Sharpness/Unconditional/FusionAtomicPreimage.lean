import Sharpness.Unconditional.FusionAtomicNormalizer
import Sharpness.FusionCentricClosure

/-! Normalizer preimages of outer-automorphism subgroups. These are the
representing objects used in the atomic comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (H : Subgroup (Aut (F.toOrbit.obj ⟨Q⟩)))

def atomicNormalizerPreimage : Subgroup S :=
  (H.comap (F.normalizerToOrbitAut Q)).map (Subgroup.normalizer (Q : Set S)).subtype

theorem mem_atomicNormalizerPreimage (s : S) :
    s ∈ F.atomicNormalizerPreimage Q H ↔
      ∃ hn : s ∈ Subgroup.normalizer (Q : Set S),
        F.normalizerToOrbitAut Q ⟨s, hn⟩ ∈ H := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.property, hn⟩
  · rintro ⟨hn, ha⟩
    exact ⟨⟨s, hn⟩, ha, rfl⟩

theorem atomicNormalizerPreimage_le_normalizer :
    F.atomicNormalizerPreimage Q H ≤ Subgroup.normalizer (Q : Set S) := by
  rintro s ⟨n, _, rfl⟩
  exact n.property

theorem le_atomicNormalizerPreimage : Q ≤ F.atomicNormalizerPreimage Q H := by
  intro q hq
  let n : F.relativeNormalizer (⊤ : Subgroup S) Q :=
    ⟨q, Q.le_normalizer hq, Subgroup.mem_top _⟩
  have hn : F.normalizerToOrbitAut Q ⟨q, Q.le_normalizer hq⟩ = 1 :=
    F.subgroup_killed_by_normalizerAut ⊤ Q (x := n) hq
  exact (F.mem_atomicNormalizerPreimage Q H q).mpr ⟨Q.le_normalizer hq, hn ▸ H.one_mem⟩

instance atomicNormalizerPreimage_normal :
    (Q.subgroupOf (F.atomicNormalizerPreimage Q H)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (F.atomicNormalizerPreimage_le_normalizer Q H)

theorem atomicNormalizerPreimage_centric (hQ : F.IsCentric Q) :
    F.IsCentric (F.atomicNormalizerPreimage Q H) :=
  F.centric_overgroup hQ (F.le_atomicNormalizerPreimage Q H)

/-- The represented restriction is fixed by the prescribed outer subgroup. -/
theorem atomicNormalizerPreimage_restriction_fixed
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) {P : F.Orbit}
    (f : F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q H⟩ ⟶ P) :
    H ≤ F.orbitHomStabilizer
      (F.toOrbit.map (F.inclusion (F.le_atomicNormalizerPreimage Q H)) ≫ f) := by
  intro a ha
  obtain ⟨n, hn⟩ := hH ha
  have hmem : n.val ∈ F.atomicNormalizerPreimage Q H :=
    (F.mem_atomicNormalizerPreimage Q H n.val).mpr ⟨n.property, hn ▸ ha⟩
  let n' : F.relativeNormalizer (F.atomicNormalizerPreimage Q H) Q :=
    ⟨n.val, n.property, hmem⟩
  have hf := F.relativeNormalizerToAut_fixes_inclusion
    (F.le_atomicNormalizerPreimage Q H) n'
  have heq : F.relativeNormalizerToAut (F.atomicNormalizerPreimage Q H) Q n' = a := hn
  rw [heq] at hf
  change a.hom ≫ (F.toOrbit.map (F.inclusion _) ≫ f) = _
  rw [← Category.assoc, hf]

theorem atomicNormalizerPreimage_ne_of_nontrivial
    (hH : H ≤ (F.normalizerToOrbitAut Q).range) (hne : H ≠ ⊥) :
    F.atomicNormalizerPreimage Q H ≠ Q := by
  intro heq
  apply hne
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨n, hn⟩ := hH ha
  have hm : n.val ∈ F.atomicNormalizerPreimage Q H :=
    (F.mem_atomicNormalizerPreimage Q H n.val).mpr ⟨n.property, hn ▸ ha⟩
  rw [heq] at hm
  have hk : F.normalizerToOrbitAut Q n = 1 :=
    F.subgroup_killed_by_normalizerAut ⊤ Q
      (x := ⟨n.val, n.property, Subgroup.mem_top _⟩) hm
  exact hn.symm.trans hk

end Sharpness.FusionSystem
