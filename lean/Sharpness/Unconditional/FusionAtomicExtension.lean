import Sharpness.Unconditional.FusionAtomicPreimage
import Sharpness.Unconditional.FusionAtomicCentric

/-! Saturation extends morphisms fixed by a normalizer action. The target
of the extension is controlled by centricity, rather than left as S. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def atomicImageEquiv {Q P : F.Object} (f : Q ⟶ P) :
    Q.subgroup ≃* F.imageSubgroup f :=
  MonoidHom.ofInjective (Subtype.val_injective.comp (F.injective f.val f.property))

theorem atomicImageEquiv_allowed {Q P : F.Object} (f : Q ⟶ P) :
    F.IsHom (F.atomicImageEquiv f).toMonoidHom := (F.toImage f).property

/-- An outer automorphism fixing a fusion-orbit morphism has an actual
conjugation witness in the target group. -/
theorem fixed_normalizer_has_target_witness {Q P : Subgroup S}
    (f : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩) (n : Subgroup.normalizer (Q : Set S))
    (hfix : (F.normalizerToOrbitAut Q n).hom ≫ F.toOrbit.map f = F.toOrbit.map f) :
    ∃ r : P, ∀ x : Q,
      (f.val (Q.normalizerMonoidHom n x)).val = r.val * (f.val x).val * r.val⁻¹ := by
  change F.toOrbit.map _ ≫ F.toOrbit.map f = _ at hfix
  rw [← F.toOrbit.map_comp] at hfix
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp hfix
  refine ⟨r, fun x => ?_⟩
  have hx := congrArg (fun z : P => z.val) (hr x)
  change (f.val x).val = r.val⁻¹ * (f.val (Q.normalizerMonoidHom n x)).val * r.val at hx
  calc
    _ = r.val * (r.val⁻¹ * (f.val (Q.normalizerMonoidHom n x)).val * r.val) * r.val⁻¹ := by group
    _ = _ := by rw [← hx]

theorem atomic_image_normalized_by_target_witness {Q P : Subgroup S}
    (f : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩) (n : Subgroup.normalizer (Q : Set S))
    (r : P) (hr : ∀ x : Q,
      (f.val (Q.normalizerMonoidHom n x)).val = r.val * (f.val x).val * r.val⁻¹) :
    r.val ∈ Subgroup.normalizer (F.imageSubgroup f : Set S) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Q.normalizerMonoidHom n q, hr q⟩
  · rintro ⟨q, hq⟩
    let y := (Q.normalizerMonoidHom n).symm q
    have hy : r.val * (f.val y).val * r.val⁻¹ = r.val * x * r.val⁻¹ := by
      rw [← hr y, MulEquiv.apply_symm_apply]
      exact hq
    exact ⟨y, mul_left_cancel (mul_right_cancel hy)⟩

/-- The extension supplied by saturation can be kept inside the specified
target whenever the conjugations admit witnesses in that target. -/
theorem centric_normalizer_extension (p : ℕ) (sat : F.Saturated p)
    {Q P R : Subgroup S} (hQR : Q ≤ R)
    (hRN : R ≤ Subgroup.normalizer (Q : Set S)) (hQ : F.IsCentric Q)
    (f : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩)
    (witness : ∀ n : R, ∃ r : P, ∀ x : Q,
      (f.val (Q.normalizerMonoidHom ⟨n.val, hRN n.property⟩ x)).val =
        r.val * (f.val x).val * r.val⁻¹) :
    ∃ g : R →* P, F.IsHom g ∧
      ∀ x : Q, (g ⟨x.val, hQR x.property⟩).val = (f.val x).val := by
  let L := F.imageSubgroup f
  let e := F.atomicImageEquiv f
  have he := F.atomicImageEquiv_allowed f
  have hL : F.IsCentric L := F.isoSystem.centricIn_of_iso e he hQ
  obtain ⟨N, hQN, hN, b, hb, hbQ⟩ := sat.extension e he (F.centric_fullyCentralized hL)
  have hR : R ≤ N := by
    intro n hn
    obtain ⟨r, hr⟩ := witness ⟨n, hn⟩
    have hrN := F.atomic_image_normalized_by_target_witness f ⟨n, hRN hn⟩ r hr
    rw [← SetLike.mem_coe, hN]
    refine ⟨⟨n, hRN hn⟩, rfl, ⟨r.val, hrN⟩, ?_⟩
    intro x
    apply Subtype.ext
    exact hr x
  have hCL : Subgroup.centralizer (L : Set S) ≤ L := by
    simpa only [inf_top_eq] using hL L le_top (MulEquiv.refl L) (F.id_mem L)
  have hbR : ∀ n : R, (b ⟨n.val, hR n.property⟩).val ∈ P := by
    intro n
    obtain ⟨r, hr⟩ := witness n
    let nN : N := ⟨n.val, hR n.property⟩
    have hc : r.val⁻¹ * (b nN).val ∈ Subgroup.centralizer (L : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro x ⟨q, rfl⟩
      let nq := Q.normalizerMonoidHom ⟨n.val, hRN n.property⟩ q
      have hnq : (⟨nq.val, hQN nq.property⟩ : N) =
          nN * ⟨q.val, hQN q.property⟩ * nN⁻¹ := rfl
      have hh := hbQ nq
      rw [hnq, map_mul, map_mul, map_inv] at hh
      have hq := hbQ q
      change (b nN).val * (b ⟨q.val, hQN q.property⟩).val * (b nN).val⁻¹ =
        (f.val nq).val at hh
      change (b ⟨q.val, hQN q.property⟩).val = (f.val q).val at hq
      rw [hq, hr q] at hh
      calc
        (f.val q).val * (r.val⁻¹ * (b nN).val) =
            r.val⁻¹ * (r.val * (f.val q).val * r.val⁻¹) * (b nN).val := by group
        _ = r.val⁻¹ * ((b nN).val * (f.val q).val * (b nN).val⁻¹) * (b nN).val := by rw [hh]
        _ = (r.val⁻¹ * (b nN).val) * (f.val q).val := by group
    have hm := P.mul_mem r.property (F.image_le f (hCL hc))
    simpa only [mul_inv_cancel_left] using hm
  let bR : R →* (⊤ : Subgroup S) := b.comp (subgroupInclusion R N hR)
  let g : R →* P :=
    { toFun n := ⟨(bR n).val, hbR n⟩
      map_one' := by apply Subtype.ext; exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (map_one bR)
      map_mul' x y := by apply Subtype.ext; exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (map_mul bR x y) }
  have hg : F.IsHom g := by
    apply F.codomain_restrict_mem bR (F.comp_mem _ _ (F.inclusion_mem hR) hb) le_top g
    ext x
    rfl
  exact ⟨g, hg, fun x => hbQ x⟩

end Sharpness.FusionSystem
