import Sharpness.PiHomologyClasses

/-! The actual product-homology comparison commutes with reindexing
and arbitrary component morphisms of short complexes. This is the
naturality needed for the cofaces of the subgroup cochain model. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι κ : Type u} [CommRing R]
    (S : ι → ShortComplex (ModuleCat.{u} R)) (T : κ → ShortComplex (ModuleCat.{u} R))
    (index : κ → ι) (φ : ∀ k, S (index k) ⟶ T k)

def piShortComplexMap : piShortComplex S ⟶ piShortComplex T where
  τ₁ := ModuleCat.ofHom (LinearMap.pi (fun k => (φ k).τ₁.hom.comp (LinearMap.proj (index k))))
  τ₂ := ModuleCat.ofHom (LinearMap.pi (fun k => (φ k).τ₂.hom.comp (LinearMap.proj (index k))))
  τ₃ := ModuleCat.ofHom (LinearMap.pi (fun k => (φ k).τ₃.hom.comp (LinearMap.proj (index k))))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    exact congrArg (fun h => h (x (index k))) (φ k).comm₁₂
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    exact congrArg (fun h => h (x (index k))) (φ k).comm₂₃

theorem piShortComplexMap_projection (k : κ) :
    piShortComplexMap S T index φ ≫ piShortComplexProjection T k =
      piShortComplexProjection S (index k) ≫ φ k := by
  apply ShortComplex.hom_ext <;> rfl

def piHomologyMap : ModuleCat.of R (∀ i, (S i).homology) ⟶
    ModuleCat.of R (∀ k, (T k).homology) :=
  ModuleCat.ofHom (LinearMap.pi (fun k =>
    (ShortComplex.homologyMap (φ k)).hom.comp (LinearMap.proj (index k))))

set_option backward.isDefEq.respectTransparency false in
theorem piShortComplexHomologyIso_naturality :
    (piShortComplexHomologyIso S).hom ≫ piHomologyMap S T index φ =
      ShortComplex.homologyMap (piShortComplexMap S T index φ) ≫ (piShortComplexHomologyIso T).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext k
  have hc :
      ShortComplex.homologyMap (piShortComplexProjection S (index k)) ≫
        ShortComplex.homologyMap (φ k) =
      ShortComplex.homologyMap (piShortComplexMap S T index φ) ≫
        ShortComplex.homologyMap (piShortComplexProjection T k) :=
    (ShortComplex.homologyMap_comp (piShortComplexProjection S (index k)) (φ k)).symm.trans
      ((congrArg (fun t : piShortComplex S ⟶ T k => ShortComplex.homologyMap t)
        (piShortComplexMap_projection S T index φ k).symm).trans
          (ShortComplex.homologyMap_comp (piShortComplexMap S T index φ)
            (piShortComplexProjection T k)))
  have hs := congrArg (fun h => h x) (piShortComplexHomologyIso_projection S (index k))
  have ht := congrArg (fun h => h (ShortComplex.homologyMap (piShortComplexMap S T index φ) x))
    (piShortComplexHomologyIso_projection T k)
  exact (congrArg (fun y => ShortComplex.homologyMap (φ k) y) hs).trans
    ((congrArg (fun h => h x) hc).trans ht.symm)

end Sharpness
