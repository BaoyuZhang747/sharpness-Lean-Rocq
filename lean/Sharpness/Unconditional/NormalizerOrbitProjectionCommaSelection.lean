import Sharpness.Unconditional.NormalizerOrbitExtensionJoins

/-! Uniqueness of the actual selected subchain from its subgroup cardinalities.
This does not depend on choices of simultaneous extensions or orbit lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

namespace NormalizerChainExtension
variable {P Q : Subgroup S} {σ τ : F.CentricChain}
    {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} (a : F.NormalizerChainExtension σ τ f)

theorem indices_card_eq (i : Fin (τ.length + 1)) :
    Nat.card (σ.subgroup (a.indices i)) = Nat.card (τ.subgroup i) := by
  let hle : σ.subgroup (a.indices i) ≤ a.carrier :=
    (σ.subgroup_mono (a.indices.monotone (Fin.le_last i))).trans a.chain_le
  let g : σ.subgroup (a.indices i) → τ.subgroup i := fun x =>
    ⟨(a.extension.val ⟨x.val, hle x.property⟩).val, by
      change (a.extension.val ⟨x.val, hle x.property⟩).val ∈ (τ.subgroup i : Set S)
      rw [← a.images i]
      exact ⟨⟨x.val, hle x.property⟩, x.property, rfl⟩⟩
  have hgi : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    change (a.extension.val ⟨x.val, hle x.property⟩).val =
      (a.extension.val ⟨y.val, hle y.property⟩).val at hv
    have he := F.injective a.extension.val a.extension.property (Subtype.ext hv)
    exact congrArg (fun z : a.carrier => z.val) he
  have hgs : Function.Surjective g := by
    intro y
    have hy : y.val ∈ (τ.subgroup i : Set S) := y.property
    rw [← a.images i] at hy
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x.val, hx⟩, Subtype.ext he⟩
  exact Nat.card_congr (Equiv.ofBijective g ⟨hgi, hgs⟩)

end NormalizerChainExtension

theorem CentricChain.subgroup_card_strict [Finite S] (σ : F.CentricChain) :
    StrictMono (fun i => Nat.card (σ.subgroup i)) := by
  intro i j hij
  apply lt_of_not_ge
  intro hcard
  exact (σ.subgroup_strict hij).ne
    (Subgroup.eq_of_le_of_card_ge (σ.subgroup_mono hij.le) hcard)

theorem CentricChain.selection_unique_of_card [Finite S] (σ τ : F.CentricChain)
    (e d : Fin (τ.length + 1) ↪o Fin (σ.length + 1))
    (he : ∀ i, Nat.card (σ.subgroup (e i)) = Nat.card (τ.subgroup i))
    (hd : ∀ i, Nat.card (σ.subgroup (d i)) = Nat.card (τ.subgroup i)) : e = d := by
  apply DFunLike.ext
  intro i
  apply σ.subgroup_card_strict.injective
  exact (he i).trans (hd i).symm

theorem NormalizerChainExtension.indices_unique [Finite S]
    {P Q P' Q' : Subgroup S} {σ τ : F.CentricChain}
    {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} {g : (⟨P'⟩ : F.Object) ⟶ ⟨Q'⟩}
    (a : F.NormalizerChainExtension σ τ f) (b : F.NormalizerChainExtension σ τ g) :
    a.indices = b.indices :=
  σ.selection_unique_of_card τ a.indices b.indices a.indices_card_eq b.indices_card_eq

end Sharpness.FusionSystem


