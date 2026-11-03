import Sharpness.CoproductChains

/-! Universal chain maps out of the actual direct-sum complex and
maps that reindex summands. Formulas are checked on every inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] {ι κ : Type u}
    (K : ι → ChainComplex (ModuleCat.{u} R) ℕ)

set_option backward.isDefEq.respectTransparency false in
def coproductChainsDesc {B : ChainComplex (ModuleCat.{u} R) ℕ} (a : ∀ i, K i ⟶ B) :
    coproductChains K ⟶ B :=
  ChainComplex.ofHom (fun n => moduleDirectSumDesc (fun i => (K i).X n) (fun i => (a i).f n)) (by
    intro n
    simp only [coproductChains, ChainComplex.of_d]
    apply moduleDirectSum_hom_ext
    intro i
    calc
      _ = (a i).f (n+1) ≫ B.d (n+1) n := moduleDirectSumInclusion_desc_assoc _ _ _ _
      _ = (K i).d (n+1) n ≫ (a i).f n := (a i).comm (n+1) n
      _ = (K i).d (n+1) n ≫ (moduleDirectSumInclusion (fun i => (K i).X n) i ≫
          moduleDirectSumDesc (fun i => (K i).X n) (fun i => (a i).f n)) :=
        congrArg (fun t => (K i).d (n+1) n ≫ t)
          (moduleDirectSumInclusion_desc (fun i => (K i).X n) (fun i => (a i).f n) i).symm
      _ = ((K i).d (n+1) n ≫ moduleDirectSumInclusion (fun i => (K i).X n) i) ≫
          moduleDirectSumDesc (fun i => (K i).X n) (fun i => (a i).f n) := (Category.assoc _ _ _).symm
      _ = (moduleDirectSumInclusion (fun i => (K i).X (n+1)) i ≫ coproductChainsDifferential K n) ≫
          moduleDirectSumDesc (fun i => (K i).X n) (fun i => (a i).f n) :=
        congrArg (fun t => t ≫ moduleDirectSumDesc (fun i => (K i).X n) (fun i => (a i).f n))
          (coproductChainsDifferential_inclusion K n i).symm
      _ = _ := Category.assoc _ _ _)

theorem coproductChainsInclusion_desc {B : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : ∀ i, K i ⟶ B) (i : ι) :
    coproductChainsInclusion K i ≫ coproductChainsDesc K a = a i := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact moduleDirectSumInclusion_desc _ _ _

theorem coproductChains_hom_ext {B : ChainComplex (ModuleCat.{u} R) ℕ}
    {f g : coproductChains K ⟶ B}
    (h : ∀ i, coproductChainsInclusion K i ≫ f = coproductChainsInclusion K i ≫ g) : f=g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply moduleDirectSum_hom_ext
  intro i
  exact congrArg (fun t => t.f n) (h i)

def coproductChainsMap (L : κ → ChainComplex (ModuleCat.{u} R) ℕ)
    (index : ι → κ) (f : ∀ i, K i ⟶ L (index i)) : coproductChains K ⟶ coproductChains L :=
  coproductChainsDesc K (fun i => f i ≫ coproductChainsInclusion L (index i))

@[reassoc]
theorem coproductChainsMap_inclusion (L : κ → ChainComplex (ModuleCat.{u} R) ℕ)
    (index : ι → κ) (f : ∀ i, K i ⟶ L (index i)) (i : ι) :
    coproductChainsInclusion K i ≫ coproductChainsMap K L index f =
      f i ≫ coproductChainsInclusion L (index i) := coproductChainsInclusion_desc _ _ _

end Sharpness
