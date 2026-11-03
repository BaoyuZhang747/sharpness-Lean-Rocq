import Sharpness.ShortComplexPiHomology
import Sharpness.ModuleHomologyClass

/-! The product-homology isomorphism acts on actual cycle classes
componentwise. In particular, its components are the native homology
maps induced by the actual short-complex product projections. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι : Type u} [CommRing R] (S : ι → ShortComplex (ModuleCat.{u} R))

def piModuleHomologyClass :
    ModuleCat.of R (∀ i, (S i).g.hom.ker) ⟶ ModuleCat.of R (∀ i, (S i).homology) :=
  ModuleCat.ofHom (LinearMap.pi (fun i => (moduleHomologyClass (S i)).hom.comp (LinearMap.proj i)))

set_option backward.isDefEq.respectTransparency false in
theorem piShortComplexHomologyIso_classes :
    moduleHomologyClass (piShortComplex S) ≫ (piShortComplexHomologyIso S).hom =
      (piShortComplexCyclesEquiv S).toModuleIso.hom ≫ piModuleHomologyClass S := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  let e := Submodule.Quotient.equiv _ _ (piShortComplexCyclesEquiv S)
    (piShortComplexCyclesEquiv_map_range S)
  have h₀ := (piShortComplex S).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply
    (Submodule.Quotient.mk x)
  have h₁ : e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (piShortComplexCyclesEquiv S x) := rfl
  have h₂ := piModuleQuotientIso_mk (fun i => (S i).g.hom.ker)
    (fun i => LinearMap.range (S i).moduleCatToCycles) (piShortComplexCyclesEquiv S x)
  change (S i).moduleCatHomologyIso.inv
    (((piModuleQuotientIso (fun i => (S i).g.hom.ker)
      (fun i => LinearMap.range (S i).moduleCatToCycles)).hom
        (e ((piShortComplex S).moduleCatHomologyIso.hom
          ((piShortComplex S).moduleCatHomologyIso.inv (Submodule.Quotient.mk x))))) i) = _
  have h₀' : (piShortComplex S).moduleCatHomologyIso.hom
      ((piShortComplex S).moduleCatHomologyIso.inv (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x := h₀
  have he := (congrArg e h₀').trans h₁
  have hp := (congrArg (fun y => (piModuleQuotientIso (fun i => (S i).g.hom.ker)
    (fun i => LinearMap.range (S i).moduleCatToCycles)).hom y) he).trans h₂
  exact congrArg (fun y => (S i).moduleCatHomologyIso.inv (y i)) hp

def piShortComplexProjection (i : ι) : piShortComplex S ⟶ S i where
  τ₁ := ModuleCat.ofHom (LinearMap.proj i)
  τ₂ := ModuleCat.ofHom (LinearMap.proj i)
  τ₃ := ModuleCat.ofHom (LinearMap.proj i)
  comm₁₂ := rfl
  comm₂₃ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem piShortComplexHomologyIso_projection (i : ι) :
    (piShortComplexHomologyIso S).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      ShortComplex.homologyMap (piShortComplexProjection S i) := by
  letI := moduleHomologyClass_epi (piShortComplex S)
  apply (cancel_epi (moduleHomologyClass (piShortComplex S))).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (congrArg (fun f => f x i) (piShortComplexHomologyIso_classes S)).trans
    (congrArg (fun f => f x) (moduleHomologyClass_naturality (piShortComplexProjection S i))).symm

end Sharpness
