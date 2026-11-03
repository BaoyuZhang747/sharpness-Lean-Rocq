import Sharpness.Unconditional.NormalizerOrbitPairCategory

/-! Simultaneous normalizer extensions depend only on the actual orbit map
when the target acting subgroup normalizes the target chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerChainExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q T : Subgroup S} {σ τ : F.CentricChain}

def changeCodomain {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
    (a : F.NormalizerChainExtension σ τ f) (g : (⟨P⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : ∀ x : P, (f.val x).val = (g.val x).val) :
    F.NormalizerChainExtension σ τ g where
  indices := a.indices
  carrier := a.carrier
  acting_le := a.acting_le
  chain_le := a.chain_le
  extension := a.extension
  onActing x := (a.onActing x).trans (hfg x)
  images := a.images

def inclusion (hPQ : P ≤ Q) (σ : F.CentricChain) :
    F.NormalizerChainExtension σ σ (F.inclusion hPQ) :=
  (identity P σ).changeCodomain (F.inclusion hPQ) (fun _ => rfl)

def postInner {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
    (a : F.NormalizerChainExtension σ τ f) (r : Q)
    (hQ : ∀ i, Q ≤ Subgroup.normalizer (τ.subgroup i : Set S)) :
    F.NormalizerChainExtension σ τ (f ≫ F.inner ⟨Q⟩ r) where
  indices := a.indices
  carrier := a.carrier
  acting_le := a.acting_le
  chain_le := a.chain_le
  extension := a.extension ≫ F.inner ⟨⊤⟩ ⟨r.val, Subgroup.mem_top _⟩
  onActing x := by
    change r.val⁻¹ * (a.extension.val ⟨x.val, a.acting_le x.property⟩).val * r.val =
      r.val⁻¹ * (f.val x).val * r.val
    rw [a.onActing x]
  images i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change r.val⁻¹ * (a.extension.val x).val * r.val ∈ (τ.subgroup i : Set S)
      apply (Subgroup.mem_normalizer_iff''.mp (hQ i r.property) _).mp
      change (a.extension.val x).val ∈ (τ.subgroup i : Set S)
      rw [← a.images i]
      exact ⟨x, hx, rfl⟩
    · intro hy
      have hy' : r.val * y * r.val⁻¹ ∈ (τ.subgroup i : Set S) :=
        (Subgroup.mem_normalizer_iff.mp (hQ i r.property) y).mp hy
      rw [← a.images i] at hy'
      obtain ⟨x, hx, hxy⟩ := hy'
      change (a.extension.val x).val = r.val * y * r.val⁻¹ at hxy
      refine ⟨x, hx, ?_⟩
      change r.val⁻¹ * (a.extension.val x).val * r.val = y
      rw [hxy]
      simp [mul_assoc]

def ofOrbitEq {f g : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
    (a : F.NormalizerChainExtension σ τ f)
    (hQ : ∀ i, Q ≤ Subgroup.normalizer (τ.subgroup i : Set S))
    (hfg : F.toOrbit.map f = F.toOrbit.map g) : F.NormalizerChainExtension σ τ g := by
  let r := Classical.choose ((F.orbit_map_eq_iff f g).mp hfg)
  have hr := Classical.choose_spec ((F.orbit_map_eq_iff f g).mp hfg)
  have heq : f ≫ F.inner ⟨Q⟩ r = g := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact (hr x).symm
  exact heq ▸ a.postInner r hQ

end Sharpness.FusionSystem.NormalizerChainExtension
