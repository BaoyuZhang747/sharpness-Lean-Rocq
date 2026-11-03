import Sharpness.SubsystemFunctorData
import Sharpness.SubsystemDoubleCosets
import Sharpness.SubsystemSpans
import Sharpness.RawMackey
import Sharpness.HigherLimits
import Sharpness.MackeyCovariant

/-! Full Mackey restriction to an actual subsystem over T ≤ S. The full
identity is proved from the ambient identity and the actual span and
double-coset correspondences; it is not a subsystem/reference field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {k : Type u} [CommRing k] (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    {P Q R : H.Object} (f : P ⟶ R) (g : Q ⟶ R)

local instance sourceTermFintype : Fintype (H.RawDoubleCosetTerm f g) := H.rawDoubleCosetTermFintype f g
local instance ambientTermFintype :
    Fintype (F.RawDoubleCosetTerm ((F.subsystemRawFunctor T H h).map f)
      ((F.subsystemRawFunctor T H h).map g)) := F.rawDoubleCosetTermFintype _ _

theorem subsystemFunctorData_spanOperator (u : R.subgroup) :
    H.functorDataSpanOperator (F.subsystemFunctorData T H h M) f g u =
      F.rawSpanOperator ((F.subsystemRawFunctor T H h).map f)
        ((F.subsystemRawFunctor T H h).map g) M (subgroupAmbientEquiv T R.subgroup u) := by
  let t : MackeySpan F.Orbit
      ((F.subsystemOrbitFunctor T H h).obj (H.toOrbit.obj P))
      ((F.subsystemOrbitFunctor T H h).obj (H.toOrbit.obj Q)) :=
    { apex := F.toOrbit.obj ((F.subsystemRawFunctor T H h).obj (H.spanApex f g u))
      left := F.toOrbit.map ((F.subsystemRawFunctor T H h).map (H.spanLeft f g u))
      right := F.toOrbit.map ((F.subsystemRawFunctor T H h).map (H.concreteSpan f g u).right) }
  exact M.span_operator_of_iso t
    (F.concreteOrbitSpan ((F.subsystemRawFunctor T H h).map f)
      ((F.subsystemRawFunctor T H h).map g) (subgroupAmbientEquiv T R.subgroup u))
    (F.toOrbit.mapIso (F.subsystemSpanIso T H h f g u))
    ((congrArg (fun t => F.toOrbit.map t) (F.subsystemSpan_left_square T H h f g u)).trans
      (F.toOrbit.map_comp _ _))
    ((congrArg (fun t => F.toOrbit.map t) (F.subsystemSpan_right_square T H h f g u)).trans
      (F.toOrbit.map_comp _ _))

theorem subsystemFunctorData_doubleCosetOperator (i : H.RawDoubleCosetTerm f g) :
    H.functorDataDoubleCosetOperator (F.subsystemFunctorData T H h M) f g i =
      F.rawDoubleCosetOperator ((F.subsystemRawFunctor T H h).map f)
        ((F.subsystemRawFunctor T H h).map g) M (F.subsystemDoubleCosetEquiv T H h f g i) := by
  refine Quotient.inductionOn i fun u => ?_
  exact F.subsystemFunctorData_spanOperator T H h M f g u

theorem subsystemFunctorData_raw_identity :
    ((F.subsystemFunctorData T H h M).pull (H.toOrbit.map f)).comp
      ((F.subsystemFunctorData T H h M).push (H.toOrbit.map g)) =
      ∑ i : H.RawDoubleCosetTerm f g,
        H.functorDataDoubleCosetOperator (F.subsystemFunctorData T H h M) f g i := by
  have hM := F.mackey_raw ((F.subsystemRawFunctor T H h).map f) ((F.subsystemRawFunctor T H h).map g) M
  have hsum : (∑ i : F.RawDoubleCosetTerm ((F.subsystemRawFunctor T H h).map f)
        ((F.subsystemRawFunctor T H h).map g),
      F.rawDoubleCosetOperator ((F.subsystemRawFunctor T H h).map f)
        ((F.subsystemRawFunctor T H h).map g) M i) =
      ∑ i : H.RawDoubleCosetTerm f g,
        H.functorDataDoubleCosetOperator (F.subsystemFunctorData T H h M) f g i := by
    calc
      _ = ∑ i : H.RawDoubleCosetTerm f g,
          F.rawDoubleCosetOperator ((F.subsystemRawFunctor T H h).map f)
            ((F.subsystemRawFunctor T H h).map g) M (F.subsystemDoubleCosetEquiv T H h f g i) :=
        ((F.subsystemDoubleCosetEquiv T H h f g).sum_comp _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        (F.subsystemFunctorData_doubleCosetOperator T H h M f g i).symm)
  exact hM.trans hsum

def subsystemMackey : MackeyModule.{u,u,u} k H.Orbit H.mackeyShape :=
  H.fullMackeyOfRawIdentity (F.subsystemFunctorData T H h M) (F.subsystemFunctorData_raw_identity T H h M)

def subsystemCoefficientIso : H.coefficient (F.subsystemMackey T H h M) ≅
    (F.subsystemOrbitFunctor T H h).op ⋙ F.coefficient M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def subsystemCovariantIso : (F.subsystemMackey T H h M).covariant ≅
    F.subsystemOrbitFunctor T H h ⋙ M.covariant :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end Sharpness.FusionSystem
