import Sharpness.Unconditional.GroupCohomologyInner

/-! Native cochain and cohomology transport along arbitrary group
isomorphisms, and invariance under inner changes of representatives. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G H A : Type u} [CommRing R] [Group G] [Group H]
    [AddCommGroup A] [Module R A]

def cochainPullIso (e : G ≃* H) :
    groupCohomology.inhomogeneousCochains (Rep.trivial R H A) ≅
      groupCohomology.inhomogeneousCochains (Rep.trivial R G A) where
  hom := cochainPull e.toMonoidHom
  inv := cochainPull e.symm.toMonoidHom
  hom_inv_id := by
    rw [← cochainPull_comp]
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      exact e.apply_symm_apply x
    rw [h, cochainPull_id]
  inv_hom_id := by
    rw [← cochainPull_comp]
    have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    rw [h, cochainPull_id]

def pullIso (e : G ≃* H) (n : ℕ) : value R H A n ≅ value R G A n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (cochainPullIso e)

@[simp]
theorem pullIso_hom (e : G ≃* H) (n : ℕ) :
    (pullIso (R := R) (A := A) e n).hom = pull e.toMonoidHom n := rfl

@[simp]
theorem pullIso_inv (e : G ≃* H) (n : ℕ) :
    (pullIso (R := R) (A := A) e n).inv = pull e.symm.toMonoidHom n := rfl

theorem pullLinear_target_inner (f : G →* H) (h : H) (n : ℕ) :
    pullLinear (R := R) (A := A) ((MulAut.conj h).toMonoidHom.comp f) n =
      pullLinear f n := by
  rw [pullLinear_comp, pullLinear_inner, LinearMap.comp_id]

theorem pullLinear_source_inner (f : G →* H) (g : G) (n : ℕ) :
    pullLinear (R := R) (A := A) (f.comp (MulAut.conj g).toMonoidHom) n =
      pullLinear f n := by
  rw [pullLinear_comp, pullLinear_inner, LinearMap.id_comp]

end Sharpness.OrdinaryCohomology
