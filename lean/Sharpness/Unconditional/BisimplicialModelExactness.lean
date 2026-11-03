import Sharpness.Unconditional.BisimplicialRepresentableTotalContraction
import Mathlib.Algebra.Homology.SingleHomology

/-! Actual positive exactness of both chain functors on every representable model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]

theorem chain_exactAt_of_homotopyEquiv_single₀
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {A : ModuleCat.{u} R}
    (e : HomotopyEquiv K ((ChainComplex.single₀ (ModuleCat R)).obj A))
    (n : ℕ) (hn : n ≠ 0) : K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 A n hn).of_iso
    (e.toHomologyIso n)

/-- The explicit contraction supplies a degree-one boundary for every element
in the kernel of its actual degree-zero augmentation. -/
theorem chain_boundary_of_homotopyEquiv_single₀
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {A : ModuleCat.{u} R}
    (e : HomotopyEquiv K ((ChainComplex.single₀ (ModuleCat R)).obj A))
    (x : K.X 0) (hx : e.hom.f 0 x = 0) : ∃ y : K.X 1, K.d 1 0 y = x := by
  have hc := e.homotopyHomInvId.comm 0
  simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
    zero_add, HomologicalComplex.comp_f, HomologicalComplex.id_f] at hc
  have hv := congrArg (fun a => a.hom x) hc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, ModuleCat.hom_id, LinearMap.id_apply] at hv
  rw [hx, map_zero] at hv
  refine ⟨-(e.homotopyHomInvId.hom 0 1) x, ?_⟩
  rw [map_neg, eq_neg_of_add_eq_zero_left hv.symm, neg_neg]

theorem bisimplicialRepresentableDiagonal_exactAt (R : Type u) [CommRing R]
    (p q n : ℕ) (hn : n ≠ 0) :
    (bisimplicialDiagonalChains (bisimplicialRepresentable p q) R).ExactAt n :=
  chain_exactAt_of_homotopyEquiv_single₀
    (bisimplicialRepresentableDiagonalHomotopyEquiv R p q) n hn

theorem bisimplicialRepresentableTotal_exactAt (R : Type u) [CommRing R]
    (p q n : ℕ) (hn : n ≠ 0) :
    (bisimplicialTotalChains (bisimplicialRepresentable p q) R).ExactAt n :=
  chain_exactAt_of_homotopyEquiv_single₀
    (bisimplicialRepresentableTotalHomotopyEquiv R p q) n hn

end Sharpness
