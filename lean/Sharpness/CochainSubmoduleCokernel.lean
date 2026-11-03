import Sharpness.SubmoduleCochainComplex
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! A native cokernel of a subcomplex inclusion has exactly the
expected quotient module in every degree. The comparison also records
the native cokernel projection on every representative. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.CochainSubmodules
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {T : CochainComplex (ModuleCat.{u} R) ℕ}
    {V W : Sharpness.CochainSubmodules T} (h : ∀ n, V.term n ≤ W.term n)

theorem map_component_range (n : ℕ) :
    ((map h).f n).hom.range = (V.term n).comap (W.term n).subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hy
    exact ⟨⟨y.val, hy⟩, Subtype.ext rfl⟩

def cokernelTermIso (n : ℕ) :
    (cokernel (map h)).X n ≅ ModuleCat.of R (W.term n ⧸ (V.term n).comap (W.term n).subtype) :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) (map h) ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((map h).f n) ≪≫
      (Submodule.quotEquivOfEq _ _ (map_component_range h n)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
theorem cokernelTermIso_projection (n : ℕ) :
    (cokernel.π (map h)).f n ≫ (cokernelTermIso h n).hom =
      ModuleCat.ofHom ((V.term n).comap (W.term n).subtype).mkQ := by
  let e₁ : (cokernel (map h)).X n ≅ cokernel ((map h).f n) :=
    PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) (map h)
  let e₂ := ModuleCat.cokernelIsoRangeQuotient ((map h).f n)
  let e₃ := (Submodule.quotEquivOfEq _ _ (map_component_range h n)).toModuleIso
  have hp₁ : (cokernel.π (map h)).f n ≫ e₁.hom = cokernel.π ((map h).f n) :=
    PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) (map h)
  have hp₂ : cokernel.π ((map h).f n) ≫ e₂.hom =
      ModuleCat.ofHom ((map h).f n).hom.range.mkQ :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _
  change (cokernel.π (map h)).f n ≫ (e₁.hom ≫ e₂.hom ≫ e₃.hom) = _
  rw [← Category.assoc, hp₁, ← Category.assoc, hp₂]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Submodule.quotEquivOfEq_mk _ _ (map_component_range h n) x

end Sharpness.CochainSubmodules
