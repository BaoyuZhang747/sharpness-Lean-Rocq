import Sharpness.Unconditional.InclusionMackeyBridgeSpans

/-! The image-factorization source isomorphisms preserve the double-coset
index sets and transport their actual linear summands. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q P' Q' T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (f' : P' ⟶ T) (g' : Q' ⟶ T)
    (hf : f.val.range = f'.val.range) (hg : g.val.range = g'.val.range)

def rawDoubleCosetSameRangeMap : F.RawDoubleCosetTerm f g → F.RawDoubleCosetTerm f' g' :=
  Quotient.map id (by
    intro x y h
    obtain ⟨c, hc, d, hd, hxy⟩ := DoubleCoset.rel_iff.mp h
    apply DoubleCoset.rel_iff.mpr
    refine ⟨c, ?_, d, ?_, hxy⟩
    · rw [← hf]
      exact hc
    · rw [← hg]
      exact hd)

def rawDoubleCosetSameRangeEquiv : F.RawDoubleCosetTerm f g ≃ F.RawDoubleCosetTerm f' g' where
  toFun := F.rawDoubleCosetSameRangeMap f g f' g' hf hg
  invFun := F.rawDoubleCosetSameRangeMap f' g' f g hf.symm hg.symm
  left_inv i := Quotient.inductionOn i (fun _ => rfl)
  right_inv i := Quotient.inductionOn i (fun _ => rfl)

variable [Finite S] (a : P ≅ P') (b : Q ≅ Q')
    (ha : a.hom ≫ f' = f) (hb : b.hom ≫ g' = g)
    {R : Type u} [Ring R] (E : MackeyFunctorData.{u,w} R F.Orbit)

include ha hb in
theorem functorDataDoubleCosetOperator_transport (i : F.RawDoubleCosetTerm f g) :
    F.functorDataDoubleCosetOperator E f g i =
      (E.pull (F.toOrbit.map a.hom)).comp
        ((F.functorDataDoubleCosetOperator E f' g'
          (F.rawDoubleCosetSameRangeEquiv f g f' g' hf hg i)).comp
          (E.push (F.toOrbit.map b.hom))) := by
  refine Quotient.inductionOn i fun u => ?_
  exact F.functorDataSpanOperator_transport f g f' g' a b ha hb u E

end Sharpness.FusionSystem
