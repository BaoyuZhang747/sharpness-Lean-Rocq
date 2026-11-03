import Sharpness.SingularCochains

/-! Actual products of module cochain complexes and maps which may
reindex the factors. These are the columns of the subgroup double
cochain complex; no differential or commutation law is assumed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] {ι κ : Type u}

def productCochains (K : ι → CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (∀ i, (K i).X q))
    (fun q => ModuleCat.ofHom (LinearMap.pi (fun i =>
      ((K i).d q (q+1)).hom.comp (LinearMap.proj i)))) (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext i
      exact congrArg (fun f => f (x i)) ((K i).d_comp_d q (q+1) (q+1+1)))

def productCochainsMap
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)
    (L : κ → CochainComplex (ModuleCat.{u} R) ℕ) (index : κ → ι)
    (f : ∀ k, K (index k) ⟶ L k) : productCochains K ⟶ productCochains L :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (LinearMap.pi (fun k =>
    ((f k).f q).hom.comp (LinearMap.proj (index k))))) (by
      intro q
      simp only [productCochains, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext k
      exact congrArg (fun t => t (x (index k))) ((f k).comm q (q+1)))

theorem productCochainsMap_apply
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)
    (L : κ → CochainComplex (ModuleCat.{u} R) ℕ) (index : κ → ι)
    (f : ∀ k, K (index k) ⟶ L k) (q : ℕ) (x : (productCochains K).X q) (k : κ) :
    (productCochainsMap K L index f).f q x k = (f k).f q (x (index k)) := rfl

end Sharpness
