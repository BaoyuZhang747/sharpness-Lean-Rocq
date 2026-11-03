import Sharpness.Unconditional.AbelianCentralizerKBridge
import Sharpness.Unconditional.AbelianCentralizerNormalizer
import Sharpness.Unconditional.KNormalizationProperties

/-! Restriction of the joint automorphism subgroup to centralizer
automorphisms, including the comparison of Sylow conditions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem abelianCentralizerJoinKEquiv_apply (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) (a : F.abelianCentralizerJoinK E P) (x : P) :
    (((F.abelianCentralizerJoinKEquiv E P a).val x).val).val =
      (a.val.val (subgroupAmbientEquiv (F.abelianCentralizerGroup E)
        (P ⊔ F.abelianInCentralizer E)
          ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val := by
  obtain ⟨b, hb⟩ := a.property
  let j := MonoidHom.ofInjective (F.abelianCentralizerJoinAutToAmbient_injective E P)
  have hj : j b = a := Subtype.ext hb
  rw [← hj]
  change (((((F.subgroupRestriction (F.abelianCentralizerGroup E)).centralizingAutomorphismEquiv
      (F.abelianInCentralizer E) P (F.abelianCentralizerSystem_central E).in_center)
        (j.symm (j b))).val x).val).val = _
  rw [j.symm_apply_apply]
  change ((b.val ⟨x.val, Subgroup.mem_sup_left x.property⟩).val).val =
    ((F.abelianCentralizerJoinAutToAmbient E P b).val
      (subgroupAmbientEquiv (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E)
        ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val
  simp only [abelianCentralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem abelianCentralizerJoinKEquiv_kNormalizer_intertwines (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E))
    (x : F.kNormalizer
      (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
      (F.abelianCentralizerJoinK E P))
    (n : Subgroup.normalizer (P : Set (F.abelianCentralizerGroup E)))
    (hxn : x.val = n.val.val) :
    F.abelianCentralizerJoinKEquiv E P (F.kNormalizerToAut _ _ x) =
      ⟨P.normalizerMonoidHom n, (F.abelianCentralizerSystem E).normalizerAut_allowed P n⟩ := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  apply Subtype.ext
  rw [F.abelianCentralizerJoinKEquiv_apply]
  change x.val * q.val.val * x.val⁻¹ = n.val.val * q.val.val * n.val.val⁻¹
  rw [hxn]

theorem abelianCentralizerJoinKEquiv_range (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    ((F.kNormalizerToAut
      (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
      (F.abelianCentralizerJoinK E P)).range).map (F.abelianCentralizerJoinKEquiv E P).toMonoidHom =
      ((F.abelianCentralizerSystem E).innerSylowSubgroup P).subgroupOf
        ((F.abelianCentralizerSystem E).automorphismSubgroup P) := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    have hx : x.val ∈ ambientSubgroup (F.abelianCentralizerGroup E)
        (Subgroup.normalizer (P : Set (F.abelianCentralizerGroup E))) :=
      (F.abelianCentralizer_kNormalizer_eq E P).le x.property
    obtain ⟨n, hn, hnx⟩ := hx
    have h := F.abelianCentralizerJoinKEquiv_kNormalizer_intertwines E P x ⟨n, hn⟩ hnx.symm
    change (F.abelianCentralizerJoinKEquiv E P (F.kNormalizerToAut _ _ x)).val ∈
      (F.abelianCentralizerSystem E).innerSylowSubgroup P
    rw [h]
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨n, hn⟩
    let x : F.kNormalizer
        (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
        (F.abelianCentralizerJoinK E P) :=
      ⟨n.val.val, by rw [F.abelianCentralizer_kNormalizer_eq]; exact ⟨n.val, n.property, rfl⟩⟩
    refine ⟨F.kNormalizerToAut _ _ x, ⟨x, rfl⟩, ?_⟩
    change F.abelianCentralizerJoinKEquiv E P (F.kNormalizerToAut _ _ x) = a
    rw [F.abelianCentralizerJoinKEquiv_kNormalizer_intertwines E P x n rfl]
    exact Subtype.ext hn

theorem abelianCentralizer_innerSylow_relIndex (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    ((F.abelianCentralizerSystem E).innerSylowSubgroup P).relIndex
        ((F.abelianCentralizerSystem E).automorphismSubgroup P) =
      (F.kNormalizerToAut
        (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
        (F.abelianCentralizerJoinK E P)).range.index := by
  change (((F.abelianCentralizerSystem E).innerSylowSubgroup P).subgroupOf
    ((F.abelianCentralizerSystem E).automorphismSubgroup P)).index = _
  have h := congrArg Subgroup.index (F.abelianCentralizerJoinKEquiv_range E P)
  exact h.symm.trans (Subgroup.index_map_equiv _ (F.abelianCentralizerJoinKEquiv E P))

theorem abelianCentralizer_sylow_of_fullyKNormalized (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E))
    (hPK : F.FullyKNormalized
      (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E))
      (F.abelianCentralizerJoinK E P)) :
    ¬ p ∣ ((F.abelianCentralizerSystem E).innerSylowSubgroup P).relIndex
      ((F.abelianCentralizerSystem E).automorphismSubgroup P) := by
  rw [F.abelianCentralizer_innerSylow_relIndex E P]
  exact (F.fullyKNormalized_properties p hS sat _ _ hPK).2

end Sharpness.FusionSystem
