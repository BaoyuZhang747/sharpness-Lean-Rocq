import Sharpness.Manuscript.SimpleStatements

/-!
The actual conjugacy-class index in Díaz–Park formula (4).
The relation uses conjugation by elements of the ambient subgroup, not
fusion conjugacy. Fusion conjugacy only specifies which subgroups occur.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

abbrev SimpleInclusion (Q U : Subgroup S) :=
  F.MinimalInclusionIndex (F.toOrbit.obj ⟨Q⟩) (F.toOrbit.obj ⟨U⟩)

/-- Conjugacy inside `U`, with the inverse convention used by the concrete
Mackey spans. Both directions of membership are part of this definition. -/
def simpleInsideConjugate {Q U : Subgroup S} (L K : F.SimpleInclusion Q U) : Prop :=
  ∃ t : U, ∀ x : S, x ∈ L.val ↔ t.val⁻¹ * x * t.val ∈ K.val

theorem simpleInsideConjugate_refl {Q U : Subgroup S} (L : F.SimpleInclusion Q U) :
    F.simpleInsideConjugate L L := by
  refine ⟨1, ?_⟩
  intro x
  simp

theorem simpleInsideConjugate_symm {Q U : Subgroup S}
    {L K : F.SimpleInclusion Q U} (h : F.simpleInsideConjugate L K) :
    F.simpleInsideConjugate K L := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t⁻¹, ?_⟩
  intro x
  simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel, mul_one] using (ht (t.val * x * t.val⁻¹)).symm

theorem simpleInsideConjugate_trans {Q U : Subgroup S}
    {L K J : F.SimpleInclusion Q U}
    (h : F.simpleInsideConjugate L K) (h' : F.simpleInsideConjugate K J) :
    F.simpleInsideConjugate L J := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ := h'
  refine ⟨t * s, ?_⟩
  intro x
  simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc] using
    (ht x).trans (hs (t.val⁻¹ * x * t.val))

def simpleConjugacySetoid (Q U : Subgroup S) : Setoid (F.SimpleInclusion Q U) where
  r := F.simpleInsideConjugate
  iseqv := ⟨F.simpleInsideConjugate_refl, F.simpleInsideConjugate_symm,
    F.simpleInsideConjugate_trans⟩

/-- The finite index set of formula (4), including the empty-index case. -/
def SimpleConjugacyClass (Q U : Subgroup S) := Quotient (F.simpleConjugacySetoid Q U)

instance (Q U : Subgroup S) : Finite (F.SimpleInclusion Q U) :=
  Finite.of_injective (fun x : F.SimpleInclusion Q U => (x.val : Set S))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

instance (Q U : Subgroup S) : Finite (F.SimpleConjugacyClass Q U) := by
  exact inferInstanceAs (Finite (Quotient (F.simpleConjugacySetoid Q U)))

def simpleClass {Q U : Subgroup S} (L : F.SimpleInclusion Q U) :
    F.SimpleConjugacyClass Q U := Quotient.mk _ L

def simpleClassRepresentative {Q U : Subgroup S} (c : F.SimpleConjugacyClass Q U) :
    F.SimpleInclusion Q U := Quotient.out c

@[simp] theorem simpleClass_representative {Q U : Subgroup S}
    (c : F.SimpleConjugacyClass Q U) :
    F.simpleClass (F.simpleClassRepresentative c) = c := Quotient.out_eq c

theorem simpleClass_eq_iff {Q U : Subgroup S} (L K : F.SimpleInclusion Q U) :
    F.simpleClass L = F.simpleClass K ↔ F.simpleInsideConjugate L K :=
  Quotient.eq

theorem simpleInclusion_card {Q U : Subgroup S} (L : F.SimpleInclusion Q U) :
    Nat.card L.val = Nat.card Q := by
  obtain ⟨e⟩ := L.property.2
  exact le_antisymm (F.orbitOrder_mono e.inv) (F.orbitOrder_mono e.hom)

/-- A surviving intersection term yields exactly the conjugacy relation
used in the index set, since its conjugation map is a bijection. -/
theorem simpleInsideConjugate_of_fullSpan {Q U : Subgroup S}
    (L K : F.SimpleInclusion Q U) (t : U)
    (hfull : (F.spanApex (F.inclusion (P := ⟨L.val⟩) (Q := ⟨U⟩) L.property.1)
      (F.inclusion (P := ⟨K.val⟩) (Q := ⟨U⟩) K.property.1) t).subgroup = L.val) :
    F.simpleInsideConjugate L K := by
  have hcard := (F.simpleInclusion_card L).trans (F.simpleInclusion_card K).symm
  let e := F.fullSpanTransportIso L.property.1 K.property.1 hcard t hfull
  have hs : Function.Surjective e.hom.val := by
    intro x
    refine ⟨e.inv.val x, ?_⟩
    have h := congrArg (fun f => f.val x) e.inv_hom_id
    exact h
  refine ⟨t, ?_⟩
  intro x
  constructor
  · exact (F.inclusion_spanApex_eq_iff L.property.1 K.property.1 t).mp hfull x
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨t.val⁻¹ * x * t.val, hx⟩
    have he := congrArg Subtype.val hy
    change t.val⁻¹ * y.val * t.val = t.val⁻¹ * x * t.val at he
    have hyx : y.val = x := mul_left_cancel (mul_right_cancel he)
    exact hyx ▸ y.property

/-- A representative change gives an actual fusion isomorphism whose
composite with inclusion is the old inclusion in the orbit category. -/
def simpleInsideTransport {Q U : Subgroup S} (L K : F.SimpleInclusion Q U)
    (h : F.simpleInsideConjugate L K) :
    F.toOrbit.obj ⟨L.val⟩ ≅ F.toOrbit.obj ⟨K.val⟩ :=
  let t := Classical.choose h
  let hfull := (F.inclusion_spanApex_eq_iff L.property.1 K.property.1 t).mpr
    (fun x hx => (Classical.choose_spec h x).mp hx)
  F.toOrbit.mapIso (F.fullSpanTransportIso L.property.1 K.property.1
    ((F.simpleInclusion_card L).trans (F.simpleInclusion_card K).symm) t hfull)

theorem simpleInsideTransport_inclusion {Q U : Subgroup S}
    (L K : F.SimpleInclusion Q U) (h : F.simpleInsideConjugate L K) :
    (F.simpleInsideTransport L K h).hom ≫ F.minimalInclusion K =
      F.minimalInclusion L := by
  exact F.fullSpanTransportIso_inclusion L.property.1 K.property.1
    ((F.simpleInclusion_card L).trans (F.simpleInclusion_card K).symm)
    (Classical.choose h) _

end Sharpness.FusionSystem
