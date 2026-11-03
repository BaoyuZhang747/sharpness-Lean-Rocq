import Sharpness.Unconditional.QuotientConstruction
import Sharpness.QuotientCentric

/-! Normalizer and automorphism comparisons for a central quotient.
The normalizer-cardinality argument adapts the earlier experiment's
`Chapter5/FactorSaturation.lean` to the manuscript's concrete fusion system. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

def quotientInducedEquiv {A B : Subgroup (S ⧸ Z)}
    (e : F.quotientPreimage Z A ≃* F.quotientPreimage Z B)
    (he : F.IsHom e.toMonoidHom) : A ≃* B :=
  MulEquiv.ofBijective (F.quotientInducedHom hZ ⟨e.toMonoidHom, he⟩)
    ⟨F.quotientInducedHom_injective hZ _,
      (F.quotientInducedHom_surjective_iff hZ _).mpr e.surjective⟩

theorem quotientInducedEquiv_allowed {A B : Subgroup (S ⧸ Z)}
    (e : F.quotientPreimage Z A ≃* F.quotientPreimage Z B)
    (he : F.IsHom e.toMonoidHom) :
    (F.centralQuotient hZ).IsHom (F.quotientInducedEquiv hZ e he).toMonoidHom :=
  ⟨⟨e.toMonoidHom, he⟩, rfl⟩

theorem quotient_iso_has_lift {A B : Subgroup (S ⧸ Z)} (e : A ≃* B)
    (he : (F.centralQuotient hZ).IsHom e.toMonoidHom) :
    ∃ (e' : F.quotientPreimage Z A ≃* F.quotientPreimage Z B)
      (he' : F.IsHom e'.toMonoidHom), F.quotientInducedEquiv hZ e' he' = e := by
  obtain ⟨f, hf⟩ := he
  have hs : Function.Surjective f.val :=
    (F.quotientInducedHom_surjective_iff hZ f).mp (hf ▸ e.surjective)
  let e' := MulEquiv.ofBijective f.val ⟨F.injective f.val f.property, hs⟩
  refine ⟨e', f.property, ?_⟩
  exact MulEquiv.toMonoidHom_injective hf

omit [Finite S] in
theorem quotientPreimage_normalizer (A : Subgroup (S ⧸ Z)) :
    F.quotientPreimage Z (Subgroup.normalizer (A : Set (S ⧸ Z))) =
      Subgroup.normalizer (F.quotientPreimage Z A : Set S) :=
  Subgroup.comap_normalizer_eq_of_surjective A (QuotientGroup.mk'_surjective Z)

def quotientNormalizerMap (A : Subgroup (S ⧸ Z)) :
    Subgroup.normalizer (F.quotientPreimage Z A : Set S) →*
      Subgroup.normalizer (A : Set (S ⧸ Z)) where
  toFun x := ⟨QuotientGroup.mk' Z x.val, by
    change x.val ∈ F.quotientPreimage Z (Subgroup.normalizer (A : Set (S ⧸ Z)))
    rw [F.quotientPreimage_normalizer]
    exact x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

omit [Finite S] in
theorem quotientNormalizerMap_surjective (A : Subgroup (S ⧸ Z)) :
    Function.Surjective (F.quotientNormalizerMap (Z := Z) A) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z y.val
  have hm : x ∈ Subgroup.normalizer (F.quotientPreimage Z A : Set S) := by
    rw [← F.quotientPreimage_normalizer]
    change (QuotientGroup.mk' Z) x ∈ Subgroup.normalizer (A : Set (S ⧸ Z))
    rw [hx]
    exact y.property
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

omit [Finite S] in
theorem quotientNormalizerMap_ker (A : Subgroup (S ⧸ Z)) :
    (F.quotientNormalizerMap (Z := Z) A).ker =
      Z.subgroupOf (Subgroup.normalizer (F.quotientPreimage Z A : Set S)) := by
  ext x
  constructor
  · intro hx
    exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext ((QuotientGroup.eq_one_iff x.val).mpr hx)

theorem quotientPreimage_normalizer_card (A : Subgroup (S ⧸ Z)) :
    Nat.card (Subgroup.normalizer (F.quotientPreimage Z A : Set S)) =
      Nat.card (Subgroup.normalizer (A : Set (S ⧸ Z))) * Nat.card Z := by
  let N := Subgroup.normalizer (F.quotientPreimage Z A : Set S)
  let f := F.quotientNormalizerMap (Z := Z) A
  have hZle : Z ≤ N := (QuotientGroup.le_comap_mk' Z A).trans Subgroup.le_normalizer
  have hk : Nat.card f.ker = Nat.card Z := by
    rw [F.quotientNormalizerMap_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv
  calc
    Nat.card N = Nat.card (N ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card f.range * Nat.card f.ker := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    _ = Nat.card (Subgroup.normalizer (A : Set (S ⧸ Z))) * Nat.card Z := by
      rw [hk, MonoidHom.range_eq_top.mpr (F.quotientNormalizerMap_surjective A)]
      simp

theorem quotientPreimage_fullyNormalized (A : Subgroup (S ⧸ Z))
    (hA : (F.centralQuotient hZ).FullyNormalized A) :
    F.FullyNormalized (F.quotientPreimage Z A) := by
  intro Q e he
  have hZQ := (F.central_containment_iff hZ e he).mp (QuotientGroup.le_comap_mk' Z A)
  let B := Q.map (QuotientGroup.mk' Z)
  have hQ : F.quotientPreimage Z B = Q := F.quotientPreimage_map hZQ
  let e' := e.trans (MulEquiv.subgroupCongr hQ.symm)
  have he' : F.IsHom e'.toMonoidHom :=
    F.comp_mem _ _ he (F.subgroupCongr_allowed hQ.symm)
  have hbar := hA B (F.quotientInducedEquiv hZ e' he')
    (F.quotientInducedEquiv_allowed hZ e' he')
  rw [← hQ, F.quotientPreimage_normalizer_card, F.quotientPreimage_normalizer_card]
  exact Nat.mul_le_mul_right _ hbar

theorem centralQuotient_fullyNormalized_iff (A : Subgroup (S ⧸ Z)) :
    (F.centralQuotient hZ).FullyNormalized A ↔
      F.FullyNormalized (F.quotientPreimage Z A) := by
  refine ⟨F.quotientPreimage_fullyNormalized hZ A, ?_⟩
  intro hA B e he
  obtain ⟨e', he', _⟩ := F.quotient_iso_has_lift hZ e he
  have h := hA (F.quotientPreimage Z B) e' he'
  rw [F.quotientPreimage_normalizer_card, F.quotientPreimage_normalizer_card] at h
  exact (Nat.mul_le_mul_right_iff (Nat.card_pos (α := Z))).mp h

/-- The surjective map on fusion automorphism groups induced by the quotient. -/
def centralQuotientAutMap (A : Subgroup (S ⧸ Z)) :
    F.automorphismSubgroup (F.quotientPreimage Z A) →*
      (F.centralQuotient hZ).automorphismSubgroup A where
  toFun a := ⟨F.quotientInducedEquiv hZ a.val a.property,
    F.quotientInducedEquiv_allowed hZ a.val a.property⟩
  map_one' := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    exact F.quotientInducedHom_apply hZ _ x
  map_mul' a b := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := F.subgroupProjection_surjective Z A x
    change F.quotientInducedHom hZ ⟨(a * b).val.toMonoidHom, (a * b).property⟩
        (F.subgroupProjection Z A y) =
      F.quotientInducedHom hZ ⟨a.val.toMonoidHom, a.property⟩
        (F.quotientInducedHom hZ ⟨b.val.toMonoidHom, b.property⟩
          (F.subgroupProjection Z A y))
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply,
      F.quotientInducedHom_apply]
    rfl

theorem centralQuotientAutMap_surjective (A : Subgroup (S ⧸ Z)) :
    Function.Surjective (F.centralQuotientAutMap hZ A) := by
  intro a
  obtain ⟨a', ha', he⟩ := F.quotient_iso_has_lift hZ a.val a.property
  exact ⟨⟨a', ha'⟩, Subtype.ext he⟩

theorem centralQuotientAutMap_normalizer (A : Subgroup (S ⧸ Z))
    (n : Subgroup.normalizer (F.quotientPreimage Z A : Set S)) :
    F.centralQuotientAutMap hZ A
        ⟨(F.quotientPreimage Z A).normalizerMonoidHom n,
          F.normalizerAut_allowed _ n⟩ =
      ⟨A.normalizerMonoidHom (F.quotientNormalizerMap A n),
        (F.centralQuotient hZ).normalizerAut_allowed _ _⟩ := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
  change F.quotientInducedHom hZ _ (F.subgroupProjection Z A x) = _
  rw [F.quotientInducedHom_apply]
  apply Subtype.ext
  change (QuotientGroup.mk' Z) (n.val * x.val * n.val⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

theorem centralQuotientAutMap_innerSylow (A : Subgroup (S ⧸ Z)) :
    ((F.innerSylowSubgroup (F.quotientPreimage Z A)).subgroupOf
      (F.automorphismSubgroup (F.quotientPreimage Z A))).map
        (F.centralQuotientAutMap hZ A) =
      ((F.centralQuotient hZ).innerSylowSubgroup A).subgroupOf
        ((F.centralQuotient hZ).automorphismSubgroup A) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨n, hn⟩ := hb
    have he : b = ⟨(F.quotientPreimage Z A).normalizerMonoidHom n,
        F.normalizerAut_allowed _ n⟩ := Subtype.ext hn.symm
    rw [he, F.centralQuotientAutMap_normalizer]
    exact ⟨F.quotientNormalizerMap A n, rfl⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := F.quotientNormalizerMap_surjective A n
    refine ⟨⟨(F.quotientPreimage Z A).normalizerMonoidHom m,
      F.normalizerAut_allowed _ m⟩, ⟨m, rfl⟩, ?_⟩
    rw [F.centralQuotientAutMap_normalizer]
    apply Subtype.ext
    change A.normalizerMonoidHom (F.quotientNormalizerMap A m) = a.val
    rw [hm]
    exact hn

/-- The Sylow clause of quotient saturation follows already from the
surjective automorphism map and the normalizer comparison. -/
theorem centralQuotient_sylow (p : ℕ) (sat : F.Saturated p)
    (A : Subgroup (S ⧸ Z)) (hA : (F.centralQuotient hZ).FullyNormalized A) :
    ¬ p ∣ ((F.centralQuotient hZ).innerSylowSubgroup A).relIndex
      ((F.centralQuotient hZ).automorphismSubgroup A) := by
  have hp := (sat.fully_normalized (F.quotientPreimage Z A)
    (F.quotientPreimage_fullyNormalized hZ A hA)).2
  intro h
  apply hp
  change p ∣ (((F.centralQuotient hZ).innerSylowSubgroup A).subgroupOf
    ((F.centralQuotient hZ).automorphismSubgroup A)).index at h
  rw [← F.centralQuotientAutMap_innerSylow hZ A] at h
  exact h.trans (Subgroup.index_map_dvd _ (F.centralQuotientAutMap_surjective hZ A))

theorem centralQuotientAutMap_ker (A : Subgroup (S ⧸ Z)) :
    (F.centralQuotientAutMap hZ A).ker =
      F.Gamma hZ (QuotientGroup.le_comap_mk' Z A) := by
  ext a
  change F.centralQuotientAutMap hZ A a = 1 ↔
    a ∈ (quotientAutomorphismAction
      (F.automorphismSubgroup (F.quotientPreimage Z A)).subtype
      (Z.subgroupOf (F.quotientPreimage Z A))
      (F.central_aut_fixed hZ (QuotientGroup.le_comap_mk' Z A))).ker
  rw [quotient_kernel_iff]
  constructor
  · intro h x
    have he := congrArg (fun b : (F.centralQuotient hZ).automorphismSubgroup A =>
      b.val (F.subgroupProjection Z A x)) h
    change F.quotientInducedHom hZ ⟨a.val.toMonoidHom, a.property⟩
      (F.subgroupProjection Z A x) = F.subgroupProjection Z A x at he
    rw [F.quotientInducedHom_apply] at he
    change x.val⁻¹ * (a.val x).val ∈ Z
    exact QuotientGroup.eq.mp (congrArg Subtype.val he).symm
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A b
    change F.quotientInducedHom hZ ⟨a.val.toMonoidHom, a.property⟩
      (F.subgroupProjection Z A x) = F.subgroupProjection Z A x
    rw [F.quotientInducedHom_apply]
    apply Subtype.ext
    change (QuotientGroup.mk (a.val x).val : S ⧸ Z) = QuotientGroup.mk x.val
    have hx : x.val⁻¹ * (a.val x).val ∈ Z := h x
    exact (QuotientGroup.eq.mpr hx).symm

theorem centralQuotientAutMap_ker_le_innerSylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (A : Subgroup (S ⧸ Z)) (hA : F.FullyNormalized (F.quotientPreimage Z A)) :
    (F.centralQuotientAutMap hZ A).ker ≤
      (F.innerSylowSubgroup (F.quotientPreimage Z A)).subgroupOf
        (F.automorphismSubgroup (F.quotientPreimage Z A)) := by
  rw [F.centralQuotientAutMap_ker]
  exact F.normal_p_subgroup_le_conjugation p hS sat _ hA _
    (F.gamma_isPGroup hZ (QuotientGroup.le_comap_mk' Z A) p hS)

end Sharpness.FusionSystem
