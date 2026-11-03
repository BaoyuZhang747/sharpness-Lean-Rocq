import Sharpness.PiModuleQuotient
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Native homology commutes with an arbitrary product of short
complexes of modules. The cycle equivalence, the image submodule, and
the quotient comparison are constructed directly. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι : Type u} [CommRing R] (S : ι → ShortComplex (ModuleCat.{u} R))

def piShortComplex : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (∀ i, (S i).X₁)
  X₂ := ModuleCat.of R (∀ i, (S i).X₂)
  X₃ := ModuleCat.of R (∀ i, (S i).X₃)
  f := ModuleCat.ofHom (LinearMap.pi (fun i => (S i).f.hom.comp (LinearMap.proj i)))
  g := ModuleCat.ofHom (LinearMap.pi (fun i => (S i).g.hom.comp (LinearMap.proj i)))
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact (S i).moduleCat_zero_apply (x i)

def piShortComplexCyclesEquiv :
    (piShortComplex S).g.hom.ker ≃ₗ[R] ∀ i, (S i).g.hom.ker where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext (fun i => (y i).property)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := funext (fun i => Subtype.ext rfl)
  map_add' x y := funext (fun i => Subtype.ext rfl)
  map_smul' r x := funext (fun i => Subtype.ext rfl)

theorem piShortComplexCyclesEquiv_map_range :
    (LinearMap.range (piShortComplex S).moduleCatToCycles).map
      (piShortComplexCyclesEquiv S).toLinearMap =
    Submodule.pi Set.univ (fun i => LinearMap.range (S i).moduleCatToCycles) := by
  ext y
  constructor
  · rintro ⟨x, ⟨b, rfl⟩, rfl⟩
    intro i _
    exact ⟨b i, rfl⟩
  · intro hy
    choose b hb using fun i => hy i (Set.mem_univ i)
    refine ⟨(piShortComplexCyclesEquiv S).symm y, ?_,
      (piShortComplexCyclesEquiv S).apply_symm_apply y⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (hb i)

def piShortComplexHomologyIso :
    (piShortComplex S).homology ≅ ModuleCat.of R (∀ i, (S i).homology) :=
  (piShortComplex S).moduleCatHomologyIso ≪≫
    (Submodule.Quotient.equiv _ _ (piShortComplexCyclesEquiv S)
      (piShortComplexCyclesEquiv_map_range S)).toModuleIso ≪≫
    piModuleQuotientIso (fun i => (S i).g.hom.ker)
      (fun i => LinearMap.range (S i).moduleCatToCycles) ≪≫
    (LinearEquiv.piCongrRight (fun i => (S i).moduleCatHomologyIso.symm.toLinearEquiv)).toModuleIso

end Sharpness
