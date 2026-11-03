import Sharpness.Unconditional.TraceFormula
import Sharpness.Unconditional.TraceFormulaSpans

/-! The image of restriction at a minimal subgroup is already the image of
restriction after its own transfer. Cross transfers either vanish by
minimality or differ from this self transfer by an actual conjugation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {L K T : Subgroup S} (hLT : L ≤ T) (hKT : K ≤ T)

/-- A full-size intersection between equal-order subgroups supplies the
actual conjugation isomorphism used to compare their transfer maps. -/
def fullSpanTransportIso (hcard : Nat.card L = Nat.card K) (t : T)
    (hfull : (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup = L) :
    (⟨L⟩ : F.Object) ≅ ⟨K⟩ :=
  F.isoOfEqualOrder
    ⟨subgroupConjugation L K t.val
        ((F.inclusion_spanApex_eq_iff hLT hKT t).mp hfull),
      F.conjugation_mem _ _ _ _⟩ hcard

theorem fullSpanTransportIso_inclusion (hcard : Nat.card L = Nat.card K) (t : T)
    (hfull : (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup = L) :
    (F.toOrbit.mapIso (F.fullSpanTransportIso hLT hKT hcard t hfull)).hom ≫
        F.toOrbit.map (F.inclusion hKT) = F.toOrbit.map (F.inclusion hLT) := by
  change F.toOrbit.map _ ≫ F.toOrbit.map _ = _
  rw [← F.toOrbit.map_comp]
  have he : (F.fullSpanTransportIso hLT hKT hcard t hfull).hom ≫ F.inclusion hKT =
      F.inclusion hLT ≫ F.inner ⟨T⟩ t := by
    apply Subtype.ext
    ext x
    rfl
  rw [he]
  exact F.orbit_map_post_inner _ _

variable {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M)

/-- This image equality is an unconditional consequence of simplicity,
minimality and the full Mackey formula. -/
theorem minimal_restriction_range_eq_self_transfer
    (hL : Nonempty (label.Q ≅ F.toOrbit.obj ⟨L⟩)) :
    LinearMap.range (M.pull (F.toOrbit.map (F.inclusion hLT))) =
      LinearMap.range ((M.pull (F.toOrbit.map (F.inclusion hLT))).comp
        (M.push (F.toOrbit.map (F.inclusion hLT)))) := by
  classical
  obtain ⟨eL⟩ := hL
  have hLorder : F.orbitOrder (F.toOrbit.obj ⟨L⟩) = F.orbitOrder label.Q :=
    le_antisymm (F.orbitOrder_mono eL.inv) (F.orbitOrder_mono eL.hom)
  apply le_antisymm
  · apply F.restriction_range_le_of_minimal_transfers M label
    intro J
    obtain ⟨eJ⟩ := J.property.2
    have hcard : Nat.card L = Nat.card J.val :=
      hLorder.trans (le_antisymm (F.orbitOrder_mono eJ.hom) (F.orbitOrder_mono eJ.inv))
    by_cases hfull : ∃ t : T,
        (F.spanApex (F.inclusion hLT) (F.inclusion (P := ⟨J.val⟩) (Q := ⟨T⟩) J.property.1) t).subgroup = L
    · obtain ⟨t, ht⟩ := hfull
      let e := F.toOrbit.mapIso (F.fullSpanTransportIso hLT J.property.1 hcard t ht)
      have hs : e.hom ≫ F.toOrbit.map (F.inclusion (P := ⟨J.val⟩) (Q := ⟨T⟩) J.property.1) =
          F.toOrbit.map (F.inclusion hLT) :=
        F.fullSpanTransportIso_inclusion hLT J.property.1 hcard t ht
      have hf : F.toOrbit.map (F.inclusion (P := ⟨J.val⟩) (Q := ⟨T⟩) J.property.1) =
          e.inv ≫ F.toOrbit.map (F.inclusion hLT) := by
        rw [← hs, Iso.inv_hom_id_assoc]
      have hf' : F.minimalInclusion J = e.inv ≫ F.toOrbit.map (F.inclusion hLT) := hf
      rintro x ⟨y, rfl⟩
      refine ⟨M.push e.inv y, ?_⟩
      change M.pull _ (M.push _ (M.push e.inv y)) = M.pull _ (M.push _ y)
      rw [hf', M.push_comp]
      rfl
    · have hz := F.minimal_mackey_raw_eq_zero M label (F.inclusion hLT)
        (F.inclusion (P := ⟨J.val⟩) (Q := ⟨T⟩) J.property.1) hLorder (fun t ht =>
          hfull ⟨t, F.inclusion_spanApex_eq_of_order hLT J.property.1 t
            (ht.trans hLorder.symm)⟩)
      change LinearMap.range ((M.pull (F.toOrbit.map (F.inclusion hLT))).comp
        (M.push (F.toOrbit.map (F.inclusion (P := ⟨J.val⟩) (Q := ⟨T⟩) J.property.1)))) ≤ _
      rw [hz, LinearMap.range_zero]
      exact bot_le
  · rintro x ⟨y, rfl⟩
    exact ⟨M.push (F.toOrbit.map (F.inclusion hLT)) y, rfl⟩

end Sharpness.FusionSystem
