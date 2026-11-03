import Sharpness.ProductCochainHomology
import Sharpness.PiHomologyNaturality

/-! The actual product-cochain cohomology comparison is natural for
arbitrary reindexing and component cochain maps, with its map fixed by
the native homology maps rather than a choice of vector-space bases. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι κ : Type u} [CommRing R]
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)
    (L : κ → CochainComplex (ModuleCat.{u} R) ℕ)
    (index : κ → ι) (φ : ∀ k, K (index k) ⟶ L k) (n : ℕ)

def piCochainHomologyMap : ModuleCat.of R (∀ i, (K i).homology n) ⟶
    ModuleCat.of R (∀ k, (L k).homology n) :=
  ModuleCat.ofHom (LinearMap.pi (fun k =>
    (HomologicalComplex.homologyMap (φ k) n).hom.comp (LinearMap.proj (index k))))

theorem productCochainsShortComplexIso_naturality :
    (productCochainsShortComplexIso K n).hom ≫
        piShortComplexMap (fun i => (K i).sc n) (fun k => (L k).sc n) index
          (fun k => (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map (φ k)) =
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map
          (productCochainsMap K L index φ) ≫ (productCochainsShortComplexIso L n).hom := by
  apply ShortComplex.hom_ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem productCochainsHomologyIso_naturality :
    HomologicalComplex.homologyMap (productCochainsMap K L index φ) n ≫
        (productCochainsHomologyIso L n).hom =
      (productCochainsHomologyIso K n).hom ≫ piCochainHomologyMap K L index φ n := by
  let ψ := fun k =>
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map (φ k)
  let f := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map
    (productCochainsMap K L index φ)
  let g := piShortComplexMap (fun i => (K i).sc n) (fun k => (L k).sc n) index ψ
  have hc : ShortComplex.homologyMap f ≫
      ShortComplex.homologyMap (productCochainsShortComplexIso L n).hom =
    ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫ ShortComplex.homologyMap g :=
    (ShortComplex.homologyMap_comp f (productCochainsShortComplexIso L n).hom).symm.trans
      ((congrArg (fun t : (productCochains K).sc n ⟶ piShortComplex (fun k => (L k).sc n) =>
          ShortComplex.homologyMap t) (productCochainsShortComplexIso_naturality K L index φ n).symm).trans
        (ShortComplex.homologyMap_comp (productCochainsShortComplexIso K n).hom g))
  have hp : (piShortComplexHomologyIso (fun i => (K i).sc n)).hom ≫
      piCochainHomologyMap K L index φ n =
    ShortComplex.homologyMap g ≫ (piShortComplexHomologyIso (fun k => (L k).sc n)).hom :=
    piShortComplexHomologyIso_naturality (fun i => (K i).sc n) (fun k => (L k).sc n) index ψ
  change ShortComplex.homologyMap f ≫
      (ShortComplex.homologyMap (productCochainsShortComplexIso L n).hom ≫
        (piShortComplexHomologyIso (fun k => (L k).sc n)).hom) =
    (ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫
      (piShortComplexHomologyIso (fun i => (K i).sc n)).hom) ≫ piCochainHomologyMap K L index φ n
  calc
    _ = (ShortComplex.homologyMap f ≫ ShortComplex.homologyMap (productCochainsShortComplexIso L n).hom) ≫
        (piShortComplexHomologyIso (fun k => (L k).sc n)).hom := (Category.assoc _ _ _).symm
    _ = (ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫ ShortComplex.homologyMap g) ≫
        (piShortComplexHomologyIso (fun k => (L k).sc n)).hom :=
      congrArg (fun t => t ≫ (piShortComplexHomologyIso (fun k => (L k).sc n)).hom) hc
    _ = ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫
        (ShortComplex.homologyMap g ≫ (piShortComplexHomologyIso (fun k => (L k).sc n)).hom) :=
      Category.assoc _ _ _
    _ = _ := (congrArg (fun t => ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫ t)
      hp.symm).trans (Category.assoc _ _ _).symm

end Sharpness
