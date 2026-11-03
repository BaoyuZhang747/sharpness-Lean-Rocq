import Sharpness.Unconditional.CentralizerSaturationKBridge
import Sharpness.Unconditional.CentralizerSaturationNormalizer
import Sharpness.Unconditional.KNormalizationProperties

/-! Restriction of the joint automorphism subgroup to centralizer
automorphisms, including the comparison of Sylow conditions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centralizerJoinKEquiv_apply (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) (a : F.centralizerJoinK p E P) (x : P) :
    (((F.centralizerJoinKEquiv p E P a).val x).val).val =
      (a.val.val (subgroupAmbientEquiv (F.centralizerGroup p E)
        (P ⊔ F.elementaryInCentralizer p E)
          ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val := by
  obtain ⟨b, hb⟩ := a.property
  let j := MonoidHom.ofInjective (F.centralizerJoinAutToAmbient_injective p E P)
  have hj : j b = a := Subtype.ext hb
  rw [← hj]
  change (((((F.subgroupRestriction (F.centralizerGroup p E)).centralizingAutomorphismEquiv
      (F.elementaryInCentralizer p E) P (F.centralizerSystem_central p E).in_center)
        (j.symm (j b))).val x).val).val = _
  rw [j.symm_apply_apply]
  change ((b.val ⟨x.val, Subgroup.mem_sup_left x.property⟩).val).val =
    ((F.centralizerJoinAutToAmbient p E P b).val
      (subgroupAmbientEquiv (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E)
        ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val
  simp only [centralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem centralizerJoinKEquiv_kNormalizer_intertwines (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E))
    (x : F.kNormalizer
      (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
      (F.centralizerJoinK p E P))
    (n : Subgroup.normalizer (P : Set (F.centralizerGroup p E)))
    (hxn : x.val = n.val.val) :
    F.centralizerJoinKEquiv p E P (F.kNormalizerToAut _ _ x) =
      ⟨P.normalizerMonoidHom n, (F.centralizerSystem p E).normalizerAut_allowed P n⟩ := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  apply Subtype.ext
  rw [F.centralizerJoinKEquiv_apply]
  change x.val * q.val.val * x.val⁻¹ = n.val.val * q.val.val * n.val.val⁻¹
  rw [hxn]

theorem centralizerJoinKEquiv_range (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    ((F.kNormalizerToAut
      (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
      (F.centralizerJoinK p E P)).range).map (F.centralizerJoinKEquiv p E P).toMonoidHom =
      ((F.centralizerSystem p E).innerSylowSubgroup P).subgroupOf
        ((F.centralizerSystem p E).automorphismSubgroup P) := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    have hx : x.val ∈ ambientSubgroup (F.centralizerGroup p E)
        (Subgroup.normalizer (P : Set (F.centralizerGroup p E))) :=
      (F.centralizer_kNormalizer_eq p E P).le x.property
    obtain ⟨n, hn, hnx⟩ := hx
    have h := F.centralizerJoinKEquiv_kNormalizer_intertwines p E P x ⟨n, hn⟩ hnx.symm
    change (F.centralizerJoinKEquiv p E P (F.kNormalizerToAut _ _ x)).val ∈
      (F.centralizerSystem p E).innerSylowSubgroup P
    rw [h]
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨n, hn⟩
    let x : F.kNormalizer
        (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
        (F.centralizerJoinK p E P) :=
      ⟨n.val.val, by rw [F.centralizer_kNormalizer_eq]; exact ⟨n.val, n.property, rfl⟩⟩
    refine ⟨F.kNormalizerToAut _ _ x, ⟨x, rfl⟩, ?_⟩
    change F.centralizerJoinKEquiv p E P (F.kNormalizerToAut _ _ x) = a
    rw [F.centralizerJoinKEquiv_kNormalizer_intertwines p E P x n rfl]
    exact Subtype.ext hn

theorem centralizer_innerSylow_relIndex (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    ((F.centralizerSystem p E).innerSylowSubgroup P).relIndex
        ((F.centralizerSystem p E).automorphismSubgroup P) =
      (F.kNormalizerToAut
        (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
        (F.centralizerJoinK p E P)).range.index := by
  change (((F.centralizerSystem p E).innerSylowSubgroup P).subgroupOf
    ((F.centralizerSystem p E).automorphismSubgroup P)).index = _
  have h := congrArg Subgroup.index (F.centralizerJoinKEquiv_range p E P)
  exact h.symm.trans (Subgroup.index_map_equiv _ (F.centralizerJoinKEquiv p E P))

theorem centralizer_sylow_of_fullyKNormalized (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E))
    (hPK : F.FullyKNormalized
      (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
      (F.centralizerJoinK p E P)) :
    ¬ p ∣ ((F.centralizerSystem p E).innerSylowSubgroup P).relIndex
      ((F.centralizerSystem p E).automorphismSubgroup P) := by
  rw [F.centralizer_innerSylow_relIndex p E P]
  exact (F.fullyKNormalized_properties p hS sat _ _ hPK).2

end Sharpness.FusionSystem
