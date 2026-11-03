import Sharpness.NormalizerAction
import Sharpness.RawMackey

/-! The actual normalizer quotient parametrizes exactly those inclusion
double cosets represented by elements normalizing the subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S)
    {T L : Subgroup S} (hLT : L ≤ T)

theorem inclusion_range_mem_iff (x : T) :
    x ∈ (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range ↔ x.val ∈ L := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩

abbrev InclusionDoubleCosets :=
  F.RawDoubleCosetTerm (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT)
    (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT)

abbrev NormalizingDoubleCosets :=
  {i : F.InclusionDoubleCosets hLT | i.out.val ∈ Subgroup.normalizer (L : Set S)}

theorem normalizer_doubleCoset_mk_eq_iff
    (n m : F.relativeNormalizer T L) :
    DoubleCoset.mk (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (⟨n.val, n.property.2⟩ : T) =
    DoubleCoset.mk (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (⟨m.val, m.property.2⟩ : T) ↔
    (QuotientGroup.mk n : F.NormalizerQuotient T L) = QuotientGroup.mk m := by
  rw [DoubleCoset.eq, QuotientGroup.eq]
  constructor
  · rintro ⟨a, ha, b, hb, hm⟩
    have haL := (F.inclusion_range_mem_iff hLT a).mp ha
    have hbL := (F.inclusion_range_mem_iff hLT b).mp hb
    have hc : n.val⁻¹ * a.val * n.val ∈ L := by
      have hi := (Subgroup.normalizer (L : Set S)).inv_mem n.property.1
      have hi' := (hi a.val).mp haL
      change n.val⁻¹ * a.val * (n.val⁻¹)⁻¹ ∈ L at hi'
      simpa only [inv_inv] using hi'
    change n.val⁻¹ * m.val ∈ L
    have hmS : m.val = a.val * n.val * b.val := congrArg Subtype.val hm
    rw [hmS]
    simpa only [mul_assoc] using L.mul_mem hc hbL
  · intro hnm
    refine ⟨1, (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range.one_mem,
      ⟨(n⁻¹ * m).val, (n⁻¹ * m).property.2⟩,
      (F.inclusion_range_mem_iff hLT _).mpr hnm, ?_⟩
    apply Subtype.ext
    simp

def normalizerDoubleCosetMap :
    F.NormalizerQuotient T L → F.InclusionDoubleCosets hLT :=
  Quotient.lift (fun n : F.relativeNormalizer T L =>
    DoubleCoset.mk (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (⟨n.val, n.property.2⟩ : T))
    (fun n m h => (F.normalizer_doubleCoset_mk_eq_iff hLT n m).mpr (Quotient.sound h))

theorem normalizerDoubleCosetMap_mk (n : F.relativeNormalizer T L) :
    F.normalizerDoubleCosetMap hLT (QuotientGroup.mk n) =
    DoubleCoset.mk (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (⟨n.val, n.property.2⟩ : T) := rfl

theorem normalizerDoubleCosetMap_injective :
    Function.Injective (F.normalizerDoubleCosetMap hLT) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun n m he => ?_
  exact (F.normalizer_doubleCoset_mk_eq_iff hLT n m).mp he

theorem normalizerDoubleCosetMap_out_mem (x : F.NormalizerQuotient T L) :
    (F.normalizerDoubleCosetMap hLT x).out.val ∈ Subgroup.normalizer (L : Set S) := by
  refine Quotient.inductionOn x fun n => ?_
  obtain ⟨a, b, ha, hb, ho⟩ := DoubleCoset.mk_out_eq_mul
    (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
    (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
    (⟨n.val, n.property.2⟩ : T)
  have haN := L.le_normalizer ((F.inclusion_range_mem_iff hLT a).mp ha)
  have hbN := L.le_normalizer ((F.inclusion_range_mem_iff hLT b).mp hb)
  rw [normalizerDoubleCosetMap_mk]
  rw [ho]
  exact (Subgroup.normalizer (L : Set S)).mul_mem
    ((Subgroup.normalizer (L : Set S)).mul_mem haN n.property.1) hbN

theorem normalizerDoubleCosetMap_range_iff (i : F.InclusionDoubleCosets hLT) :
    i ∈ Set.range (F.normalizerDoubleCosetMap hLT) ↔
      i.out.val ∈ Subgroup.normalizer (L : Set S) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact F.normalizerDoubleCosetMap_out_mem hLT x
  · intro hi
    refine ⟨QuotientGroup.mk ⟨i.out.val, hi, i.out.property⟩, ?_⟩
    exact DoubleCoset.out_eq' _ _ i

def normalizerDoubleCosetEquiv :
    F.NormalizerQuotient T L ≃ F.NormalizingDoubleCosets hLT :=
  Equiv.ofBijective
    (fun x => ⟨F.normalizerDoubleCosetMap hLT x, F.normalizerDoubleCosetMap_out_mem hLT x⟩)
    ⟨fun _ _ h => F.normalizerDoubleCosetMap_injective hLT (congrArg Subtype.val h),
      fun i => by
        obtain ⟨x, hx⟩ := (F.normalizerDoubleCosetMap_range_iff hLT i.val).mpr i.property
        exact ⟨x, Subtype.ext hx⟩⟩

theorem normalizerDoubleCosetEquiv_apply (x : F.NormalizerQuotient T L) :
    (F.normalizerDoubleCosetEquiv hLT x).val = F.normalizerDoubleCosetMap hLT x := rfl

theorem normalizerDoubleCosetEquiv_mk (n : F.relativeNormalizer T L) :
    (F.normalizerDoubleCosetEquiv hLT (QuotientGroup.mk n)).val =
    DoubleCoset.mk (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (F.inclusion (P := ⟨L⟩) (Q := ⟨T⟩) hLT).val.range
      (⟨n.val, n.property.2⟩ : T) := rfl

end Sharpness.FusionSystem
