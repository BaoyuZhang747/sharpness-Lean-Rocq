import Sharpness.Unconditional.ChainTotalHorizontalHomotopy
import Mathlib.Algebra.Homology.Single

/-! The native total of a bicomplex supported in outer degree zero is
canonically the original inner chain complex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
variable {R : Type u} [CommRing R]
variable (L : ChainComplex (ModuleCat.{u} R) ℕ)

abbrev chainOuterSingle :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (ChainComplex.single₀ (ChainComplex (ModuleCat.{u} R) ℕ)).obj L

def chainTotalOuterSingleInclusion : L ⟶ (chainOuterSingle L).total (ComplexShape.down ℕ) :=
  ChainComplex.ofHom (fun n => (chainOuterSingle L).ιTotal (ComplexShape.down ℕ) 0 n n (by simp))
    (fun n => by
      rw [HomologicalComplex₂.total_d, comp_add,
        chainTotal_horizontal_zero_outgoing (chainOuterSingle L) (n+1) n (by omega),
        chainTotal_vertical_outgoing (chainOuterSingle L) 0 n n (by omega), zero_add,
        pow_zero, one_smul]
      rfl)

def chainTotalOuterSingleProjection : (chainOuterSingle L).total (ComplexShape.down ℕ) ⟶ L :=
  ChainComplex.ofHom (fun n => chainTotalProjection (chainOuterSingle L) 0 n n (by simp))
    (fun n => by
      rw [HomologicalComplex₂.total_d, add_comp,
        chainTotal_horizontal_incoming (chainOuterSingle L) 0 n n (by omega),
        chainTotal_vertical_incoming (chainOuterSingle L) 0 n n (by omega)]
      simp only [chainOuterSingle, HomologicalComplex.single_obj_d,
        HomologicalComplex.zero_f, comp_zero, zero_add, pow_zero, one_smul]
      rfl)

def chainTotalOuterSingleIso : (chainOuterSingle L).total (ComplexShape.down ℕ) ≅ L where
  hom := chainTotalOuterSingleProjection L
  inv := chainTotalOuterSingleInclusion L
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p+q=n at hpq
    cases p with
    | zero =>
        have hqn : q=n := by omega
        subst q
        change (chainOuterSingle L).ιTotal _ 0 n n hpq ≫
          (chainTotalProjection (chainOuterSingle L) 0 n n (by simp) ≫
            (chainOuterSingle L).ιTotal _ 0 n n (by simp)) = _
        rw [← Category.assoc, chainTotalProjection_inclusion, Category.id_comp, HomologicalComplex.id_f, Category.comp_id]
    | succ p =>
        exact ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) q).map_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 L (p+1)
            (by omega))).eq_of_src _ _
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact chainTotalProjection_inclusion (chainOuterSingle L) 0 n n (by simp)

end Sharpness
