import Sharpness.Unconditional.NormalizerHigherLimitComparisonMaps
import Sharpness.Unconditional.NormalizerSubdivisionConjugacy

/-! The native normalizer diagram computes cohomology of every actual
chain-automorphism group, independently of the chosen representatives.
Its subchain maps are exactly the actual tuple-deletion homomorphisms,
under the proved comparison isomorphisms. All arguments are algebraic. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G H : Type u} [CommRing R] [Group G] [Group H]
    {A : ModuleCat.{u} R} {C : Type u} [Category.{u} C]

/-- Two one-object right adjoints into the same category give a native
cohomology comparison, induced by the actual section/reflection maps. -/
def reflectionComparisonIso
    {J : SingleObj G ⥤ C} {P : C ⥤ SingleObj G} (adj : P ⊣ J)
    {J' : SingleObj H ⥤ C} {P' : C ⥤ SingleObj H} (adj' : P' ⊣ J') (n : ℕ) :
    value R G A n ≅ value R H A n where
  hom := functorPull (J' ⋙ P) n
  inv := functorPull (J ⋙ P') n
  hom_inv_id := by
    rw [← functorPull_comp]
    have h := functorPull_eq_of_natTrans (R := R) (A := A)
      (Functor.whiskerLeft J (Functor.whiskerRight adj'.unit P)) n
    exact h.symm.trans ((functorPull_eq_of_natTrans adj.counit n).trans (functorPull_id n))
  inv_hom_id := by
    rw [← functorPull_comp]
    have h := functorPull_eq_of_natTrans (R := R) (A := A)
      (Functor.whiskerLeft J' (Functor.whiskerRight adj.unit P')) n
    exact h.symm.trans ((functorPull_eq_of_natTrans adj'.counit n).trans (functorPull_id n))

end Sharpness.OrdinaryCohomology

namespace Sharpness.NormalizerReflection
open CategoryTheory Opposite
variable {D : Type u} [Category.{u} D] (K : D ⥤ Cat.{u,u})
    (G : D → Type u) [∀ d, Group (G d)]
    (J : ∀ d, SingleObj (G d) ⥤ K.obj d)
    (P : ∀ d, K.obj d ⥤ SingleObj (G d))
    (adj : ∀ d, P d ⊣ J d)
    {R H H' : Type u} [CommRing R] [Group H] [Group H']
    {A : ModuleCat.{u} R} {d e : D}
    {T : SingleObj H ⥤ K.obj d} {U : SingleObj H' ⥤ K.obj e}

/-- Any actual comparison square of sections gives the corresponding
exact square of native group-cohomology pullbacks. -/
theorem native_comparison_naturality (f : d ⟶ e)
    (g : H →* H') (α : T ⋙ (K.map f).toFunctor ⟶ g.toFunctor ⋙ U) (n : ℕ) :
    (coefficient K G J P adj R A n).map f.op ≫
        OrdinaryCohomology.functorPull (T ⋙ P d) n =
      OrdinaryCohomology.functorPull (U ⋙ P e) n ≫
        OrdinaryCohomology.pull g n := by
  change OrdinaryCohomology.functorPull (arrowFunctor K G J P f) n ≫ _ = _
  rw [← OrdinaryCohomology.functorPull_comp]
  have hunit := OrdinaryCohomology.functorPull_eq_of_natTrans (R := R) (A := A)
    (Functor.whiskerLeft T
      (Functor.whiskerRight (adj d).unit ((K.map f).toFunctor ⋙ P e))) n
  have hsquare := OrdinaryCohomology.functorPull_eq_of_natTrans (R := R) (A := A)
    (Functor.whiskerRight α (P e)) n
  exact hunit.symm.trans (hsquare.trans (OrdinaryCohomology.functorPull_comp
    g.toFunctor (U ⋙ P e) n))

end Sharpness.NormalizerReflection

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

/-- The native quotient diagram evaluated at an arbitrary actual chain. -/
def normalizerNativeChainIso (σ : F.CentricChain) (n : ℕ) :
    (L.normalizerOrdinaryDiagram R A n).obj (op (F.normalizerClass σ)) ≅
      OrdinaryCohomology.value R (L.ChainAut σ) A n :=
  OrdinaryCohomology.reflectionComparisonIso
    (L.normalizerRepresentativeAdjunction (F.normalizerClass σ))
    (L.normalizerCommaAdjunction σ) n

/-- This is the actual deletion map on compatible tuples, including
subchains whose first subgroup differs from the original first subgroup. -/
theorem normalizerNativeChainIso_subchain (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) (n : ℕ) :
    (L.normalizerOrdinaryDiagram R A n).map (F.normalizerSubchainArrow σ m e).op ≫
        (L.normalizerNativeChainIso R A σ n).hom =
      (L.normalizerNativeChainIso R A (σ.subchain m e) n).hom ≫
        OrdinaryCohomology.pull (L.chainAutRestriction σ m e) n :=
  NormalizerReflection.native_comparison_naturality
    (CostructuredArrow.functor L.normalizerSubdivisionProjection)
    (fun d => L.ChainAut (normalizerRepresentative (F := F) d))
    L.normalizerRepresentativeComparison L.normalizerRepresentativeReflection
    L.normalizerRepresentativeAdjunction (F.normalizerSubchainArrow σ m e)
    (L.chainAutRestriction σ m e) (L.normalizerSubdivisionComparison_subchain σ m e) n

/-- Conjugacy transport uses the specified tuple conjugation, for every
compatible family of linking isomorphisms. It is not made strictly
invariant before passing to cohomology. -/
theorem normalizerNativeChainIso_conjugacy (σ τ : F.CentricChain)
    (c : CentricChain.Conjugacy σ τ)
    (a : ∀ i : Fin (σ.length + 1), σ.linkingObject L i ≅ τ.linkingObject L (c.indices i))
    (ha : ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
      (a i).hom ≫ L.chainInclusion τ (c.indices.monotone h) =
        L.chainInclusion σ h ≫ (a j).hom)
    (φ : L.ChainAut σ ≃* L.ChainAut τ)
    (hφ : ∀ (g : L.ChainAut σ) (i : Fin (σ.length + 1)),
      ((φ g).val (c.indices i)).hom = (a i).inv ≫ (g.val i).hom ≫ (a i).hom)
    (n : ℕ) :
    (L.normalizerOrdinaryDiagram R A n).map
        (eqToHom ((F.normalizerClass_eq_iff σ τ).mpr ⟨c⟩)).op ≫
        (L.normalizerNativeChainIso R A σ n).hom =
      (L.normalizerNativeChainIso R A τ n).hom ≫
        OrdinaryCohomology.pull φ.toMonoidHom n :=
  NormalizerReflection.native_comparison_naturality
    (CostructuredArrow.functor L.normalizerSubdivisionProjection)
    (fun d => L.ChainAut (normalizerRepresentative (F := F) d))
    L.normalizerRepresentativeComparison L.normalizerRepresentativeReflection
    L.normalizerRepresentativeAdjunction
    (eqToHom ((F.normalizerClass_eq_iff σ τ).mpr ⟨c⟩)) φ.toMonoidHom
    (L.normalizerSubdivisionComparison_conjugacy σ τ c a ha φ hφ).hom n

end Sharpness.FusionSystem.CentricLinkingSystem
