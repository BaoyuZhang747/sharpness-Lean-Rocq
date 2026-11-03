import Sharpness.Unconditional.TraceFormulaTransfer
import Sharpness.Unconditional.TraceDoubleCosets

/-! The normalizer trace input, proved from the full Mackey formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M)
    {T L : Subgroup S} (hLT : L ≤ T)

/-- At a minimal subgroup, restriction followed by transfer is the actual
sum over the normalizer quotient. Proper intersection terms vanish. -/
theorem minimal_self_mackey_eq_normalizerTrace
    (hL : Nonempty (label.Q ≅ F.toOrbit.obj ⟨L⟩)) :
    (M.pull (F.toOrbit.map (F.inclusion hLT))).comp
        (M.push (F.toOrbit.map (F.inclusion hLT))) =
      F.normalizerTrace M T L := by
  classical
  obtain ⟨eL⟩ := hL
  have hLorder : F.orbitOrder (F.toOrbit.obj ⟨L⟩) = F.orbitOrder label.Q :=
    le_antisymm (F.orbitOrder_mono eL.inv) (F.orbitOrder_mono eL.hom)
  rw [F.mackey_raw]
  symm
  letI : Fintype (F.NormalizerQuotient T L) := Fintype.ofFinite _
  letI : Fintype (F.InclusionDoubleCosets hLT) :=
    F.rawDoubleCosetTermFintype (F.inclusion hLT) (F.inclusion hLT)
  change (∑ a : F.NormalizerQuotient T L,
    M.push (F.normalizerQuotientToAut T L a).hom) = _
  apply Fintype.sum_of_injective (F.normalizerDoubleCosetMap hLT)
    (F.normalizerDoubleCosetMap_injective hLT)
  · intro i hi
    rw [F.rawDoubleCosetOperator_out]
    apply F.rawSpanOperator_eq_zero_of_small M label
    have hnot : i.out.val ∉ Subgroup.normalizer (L : Set S) :=
      fun hn => hi ((F.normalizerDoubleCosetMap_range_iff hLT i).mpr hn)
    have hne : F.orbitOrder (F.toOrbit.obj
        (F.spanApex (F.inclusion hLT) (F.inclusion hLT) i.out)) ≠
          F.orbitOrder label.Q := by
      intro heq
      exact hnot ((F.inclusion_self_spanApex_eq_iff_normalizer hLT i.out).mp
        (F.inclusion_spanApex_eq_of_order hLT hLT i.out (heq.trans hLorder.symm)))
    exact lt_of_le_of_ne
      ((F.orbitOrder_mono (F.toOrbit.map (F.spanLeft (F.inclusion hLT)
        (F.inclusion hLT) i.out))).trans_eq hLorder) hne
  · intro a
    refine Quotient.inductionOn a fun n => ?_
    change M.push (F.normalizerToOrbitAut L ⟨n.val, n.property.1⟩).hom =
      F.rawSpanOperator (F.inclusion hLT) (F.inclusion hLT) M
        (⟨n.val, n.property.2⟩ : T)
    exact (F.rawSpanOperator_inclusion_normalizer hLT M n).symm

/-- An unconditional constructor of the existing Díaz–Park trace input.
No semisimplicity, characteristic or saturation assumption is needed. -/
def diazParkTraceInput : F.DiazParkTraceInput (k := k) where
  equations_4_6 M label T L hLT hL := by
    rw [F.minimal_restriction_range_eq_self_transfer hLT M label hL,
      F.minimal_self_mackey_eq_normalizerTrace M label hLT hL]

end Sharpness.FusionSystem
