import Sharpness.Unconditional.NormalizerSubdivisionCommaAdjunction
import Sharpness.Unconditional.HeterogeneousNerveAdjunction
import Sharpness.SimplicialReplacementLinearization

/-! The actual chain-automorphism comparison for the normalizer comma
model is a chain homotopy equivalence over every commutative ring.
The actual adjunction is passed to the general mixed-universe
nerve-chain comparison, without a realization premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerCommaReflectionNerveMap (σ : F.CentricChain) :
    nerve (CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ)) ⟶
      nerve (SingleObj (L.ChainAut σ)) :=
  { app _ := ↾fun X => ((L.normalizerCommaReflection σ).mapComposableArrows _).obj X }

def normalizerCommaChainHomotopyEquiv (R : Type u) [CommRing R] (σ : F.CentricChain) :
    HomotopyEquiv
      ((simplicialChainsFunctor R).obj (nerve (SingleObj (L.ChainAut σ))))
      ((simplicialChainsFunctor R).obj
        (nerve (CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass σ)))) :=
  (heterogeneousNerveAdjunctionChainHomotopyEquiv
    (L.normalizerCommaAdjunction σ) (ModuleCat.of R R)).symm

theorem normalizerCommaChainHomotopyEquiv_hom (R : Type u) [CommRing R] (σ : F.CentricChain) :
    (L.normalizerCommaChainHomotopyEquiv R σ).hom =
      (simplicialChainsFunctor R).map
        (nerveMapSingleObj (L.ChainAut σ) (L.normalizerSubdivisionChainComparison σ)) := rfl

theorem normalizerCommaChainHomotopyEquiv_inv (R : Type u) [CommRing R] (σ : F.CentricChain) :
    (L.normalizerCommaChainHomotopyEquiv R σ).inv =
      (simplicialChainsFunctor R).map (L.normalizerCommaReflectionNerveMap σ) := rfl

theorem normalizerSubdivisionChainComparison_quasiIso (R : Type u) [CommRing R]
    (σ : F.CentricChain) :
    QuasiIso ((simplicialChainsFunctor R).map
      (nerveMapSingleObj (L.ChainAut σ) (L.normalizerSubdivisionChainComparison σ))) :=
  (L.normalizerCommaChainHomotopyEquiv R σ).quasiIso_hom

end Sharpness.FusionSystem.CentricLinkingSystem
