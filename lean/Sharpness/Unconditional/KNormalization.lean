import Sharpness.Unconditional.AlperinNormalizer

/-! Actual K-normalizers, for K a subgroup of the fusion automorphism group. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def kNormalizerAction (P : Subgroup S) :
    Subgroup.normalizer (P : Set S) →* F.automorphismSubgroup P where
  toFun n := ⟨P.normalizerMonoidHom n, F.normalizerAut_allowed P n⟩
  map_one' := Subtype.ext (map_one P.normalizerMonoidHom)
  map_mul' n m := Subtype.ext (map_mul P.normalizerMonoidHom n m)

def kNormalizer (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) : Subgroup S :=
  (K.comap (F.kNormalizerAction P)).map (Subgroup.normalizer (P : Set S)).subtype

theorem mem_kNormalizer_iff (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) (x : S) :
    x ∈ F.kNormalizer P K ↔ ∃ hx : x ∈ Subgroup.normalizer (P : Set S),
      F.kNormalizerAction P ⟨x, hx⟩ ∈ K := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.property, hn⟩
  · rintro ⟨hx, hK⟩
    exact ⟨⟨x, hx⟩, hK, rfl⟩

theorem kNormalizer_le_normalizer (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    F.kNormalizer P K ≤ Subgroup.normalizer (P : Set S) :=
  fun x hx => ((F.mem_kNormalizer_iff P K x).mp hx).1

def kNormalizerToAut (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    F.kNormalizer P K →* K where
  toFun x := ⟨F.kNormalizerAction P ⟨x.val, F.kNormalizer_le_normalizer P K x.property⟩,
    ((F.mem_kNormalizer_iff P K x.val).mp x.property).2⟩
  map_one' := by apply Subtype.ext; exact map_one (F.kNormalizerAction P)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (F.kNormalizerAction P)
      ⟨x.val, F.kNormalizer_le_normalizer P K x.property⟩
      ⟨y.val, F.kNormalizer_le_normalizer P K y.property⟩

theorem centralizer_le_kNormalizer (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    Subgroup.centralizer (P : Set S) ≤ F.kNormalizer P K := by
  intro x hx
  apply (F.mem_kNormalizer_iff P K x).mpr
  refine ⟨Subgroup.centralizer_le_normalizer _ hx, ?_⟩
  have h : F.kNormalizerAction P ⟨x, Subgroup.centralizer_le_normalizer _ hx⟩ = 1 := by
    apply Subtype.ext
    ext p
    change x * p.val * x⁻¹ = p.val
    rw [← (Subgroup.mem_centralizer_iff.mp hx) p.val p.property,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [h]
  exact K.one_mem

theorem kNormalizerToAut_ker (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) :
    (F.kNormalizerToAut P K).ker =
      (Subgroup.centralizer (P : Set S)).subgroupOf (F.kNormalizer P K) := by
  ext x
  constructor
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro p hp
    have h := congrArg (fun a : K => (a.val.val ⟨p, hp⟩).val) hx
    change x.val * p * x.val⁻¹ = p at h
    calc
      p * x.val = (x.val * p * x.val⁻¹) * x.val := by rw [h]
      _ = x.val * p := by group
  · intro hx
    change x.val ∈ Subgroup.centralizer (P : Set S) at hx
    apply Subtype.ext
    apply Subtype.ext
    ext p
    change x.val * p.val * x.val⁻¹ = p.val
    rw [← (Subgroup.mem_centralizer_iff.mp hx) p.val p.property,
      mul_assoc, mul_inv_cancel, mul_one]

def kTransport {P Q : Subgroup S} (e : P ≃* Q) (he : F.IsHom e.toMonoidHom)
    (K : Subgroup (F.automorphismSubgroup P)) : Subgroup (F.automorphismSubgroup Q) :=
  K.map (F.alperinAutTransport e he).toMonoidHom

def FullyKNormalized (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) : Prop :=
  ∀ (Q : Subgroup S) (e : P ≃* Q) (he : F.IsHom e.toMonoidHom),
    Nat.card (F.kNormalizer Q (F.kTransport e he K)) ≤ Nat.card (F.kNormalizer P K)

end Sharpness.FusionSystem
