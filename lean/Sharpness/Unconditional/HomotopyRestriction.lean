import Mathlib.Algebra.Homology.Homotopy

/-! Restrict an actual chain homotopy along a degreewise monomorphism. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

def restrictHomotopy {V : Type u} [Category.{v} V] [Preadditive V]
    {ι : Type w} {c : ComplexShape ι} {S K : HomologicalComplex V c}
    (i : S ⟶ K) [∀ n, Mono (i.f n)]
    {f g : S ⟶ S} {F G : K ⟶ K}
    (hf : f ≫ i = i ≫ F) (hg : g ≫ i = i ≫ G)
    (H : Homotopy F G) (h : ∀ n m, S.X n ⟶ S.X m)
    (hh : ∀ n m, h n m ≫ i.f m = i.f n ≫ H.hom n m) : Homotopy f g where
  hom := h
  zero n m hnm := by
    apply (cancel_mono (i.f m)).mp
    rw [hh, H.zero n m hnm, comp_zero, zero_comp]
  comm n := by
    apply (cancel_mono (i.f n)).mp
    have hf' := congrArg (fun a => a.f n) hf
    have hg' := congrArg (fun a => a.f n) hg
    change f.f n ≫ i.f n = i.f n ≫ F.f n at hf'
    change g.f n ≫ i.f n = i.f n ≫ G.f n at hg'
    rw [hf', H.comm, comp_add, comp_add, add_comp, add_comp, hg']
    congr 2
    · rw [← dNext_comp_right, ← dNext_comp_left]
      congr 1
      funext a b
      exact (hh a b).symm
    · rw [← prevD_comp_right, ← prevD_comp_left]
      congr 1
      funext a b
      exact (hh a b).symm

end Sharpness
