import Sharpness.LibmanNormalizerData
import Sharpness.CostructuredGrothendieckFibers
import Sharpness.Saturation
import Sharpness.SimplicialReplacementLinearization
import Mathlib.Algebra.Homology.QuasiIso

/-! The precise uniform Libman reference boundary. The reference
supplies its subdivision category, projection, and evaluation. We
construct the pushdown as the actual comma functor (projection down d),
the canonical model of Definition 3.2 for a constant one-point category.
The diagram is fixed by this construction. The categorical comparisons
and their specified squares follow the model in Theorem 5.1, printed
pp.1283-1284. Subchain squares are natural transformations, whose
components retain the initial subgroup inclusion. Conjugacy squares are recorded by natural isomorphisms,
as required by the underlying comma-category construction; strict
equality together with the evaluation factorization would incorrectly
force invariance under every inner automorphism. The canonical
component must be checked in the eventual construction of this input.
Parts (1) and (2) give weak equivalences of the actual nerves. Their
free R-chain quasi-isomorphism consequences use the already recorded
simplicial/realization homology and change-of-coefficients results,
Weibel 8.2.3-8.2.4 and 3.6.1-3.6.2. These chain consequences are
explicitly distinguished from verbatim statements in Libman.

The same fixed diagram is used for every commutative R. No coefficient
module, cohomology, higher-limit vanishing, spectral sequence, geometric
augmentation, convergence, or edge-isomorphism field occurs here.
See sources/NormalizerReferences.provenance.json. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

structure LibmanNormalizerInput (p : ℕ) [Fact p.Prime]
    (_hS : IsPGroup p S) (_sat : F.Saturated p) where
  subdivision : Cat.{u,u}
  projection : subdivision ⥤ F.NormalizerCategory
  evaluation : subdivision ⥤ L.Object
  chainComparison : ∀ σ : F.CentricChain,
    SingleObj (L.ChainAut σ) ⥤ CostructuredArrow projection (F.normalizerClass σ)
  comparison_subchain : ∀ (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)),
    chainComparison σ ⋙ CostructuredArrow.map (F.normalizerSubchainArrow σ m e) ⟶
      (L.chainAutRestriction σ m e).toFunctor ⋙ chainComparison (σ.subchain m e)
  comparison_factorization : ∀ σ : F.CentricChain,
    chainComparison σ ⋙ CostructuredArrow.proj projection (F.normalizerClass σ) ⋙ evaluation =
      L.chainAutomorphismFunctor σ
  comparison_conjugacy : ∀ (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ)
    (a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i))
    (_commutes : ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
      (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
        L.chainInclusion σ h ≫ (a j).hom)
    (φ : L.ChainAut σ ≃* L.ChainAut τ)
    (_coordinates : ∀ (g : L.ChainAut σ) (i : Fin (σ.length + 1)),
      ((φ g).val (c.indices i)).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom),
    chainComparison σ ⋙ CostructuredArrow.map
      (eqToHom ((F.normalizerClass_eq_iff σ τ).mpr ⟨c⟩)) ≅
      φ.toMonoidHom.toFunctor ⋙ chainComparison τ
  Libman_5_1_1_Weibel : ∀ (R : Type u) [CommRing R],
    QuasiIso ((simplicialChainsFunctor R).map (CategoryTheory.nerveMap
      (CostructuredArrow.grothendieckProj projection ⋙ evaluation)))
  Libman_5_1_2_Weibel : ∀ (R : Type u) [CommRing R] (σ : F.CentricChain),
    QuasiIso ((simplicialChainsFunctor R).map
      (nerveMapSingleObj (L.ChainAut σ) (chainComparison σ)))

namespace LibmanNormalizerInput
variable {L} {p : ℕ} [Fact p.Prime] {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

def toLibmanNormalizerData : L.LibmanNormalizerData where
  categoryDiagram := CostructuredArrow.functor I.projection
  toLinking := CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation
  chainComparison := I.chainComparison
  comparison_subchain := I.comparison_subchain
  comparison_factorization σ := by
    have h := congrArg (fun T => I.chainComparison σ ⋙ T ⋙ I.evaluation)
      (costructuredGrothendieckFiber_projection I.projection (F.normalizerClass σ))
    exact h.trans (I.comparison_factorization σ)
  comparison_conjugacy := I.comparison_conjugacy

end LibmanNormalizerInput

end Sharpness.FusionSystem.CentricLinkingSystem
