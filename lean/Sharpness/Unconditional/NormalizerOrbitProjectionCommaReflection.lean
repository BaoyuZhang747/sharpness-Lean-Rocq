import Sharpness.Unconditional.NormalizerOrbitProjectionCommaOpposite
import Sharpness.Unconditional.NormalizerOrbitProjectionCommaFactorization

/-! The actual Sylow-chain pointing is universal by the proved pair-extension
factorization. It yields a reflection onto the literal fixed-chain category,
and hence initiality of its opposite inclusion into the right-Kan comma category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
  (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory)

abbrev normalizerRepresentativeCommaInclusion :=
  F.normalizerAtChainToComma (L.normalizerSylowRepresentative p hS sat d) d
    (L.normalizerSylowRepresentative_class p hS sat d)

def normalizerCommaPointingObject
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d) :=
  Classical.choose (L.exists_pointing_to_sylow_chain p hS sat d X)

def normalizerCommaPointingArrow
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    X.left ⟶ (L.normalizerCommaPointingObject p hS sat d X).obj :=
  Classical.choose (Classical.choose_spec (L.exists_pointing_to_sylow_chain p hS sat d X))

theorem normalizerCommaPointingArrow_isIso
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    IsIso (F.normalizerOrbitPairForget.map (L.normalizerCommaPointingArrow p hS sat d X)) :=
  Classical.choose_spec (Classical.choose_spec (L.exists_pointing_to_sylow_chain p hS sat d X))

def normalizerCommaPointingUnit
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    X ⟶ (L.normalizerRepresentativeCommaInclusion p hS sat d).obj
      (L.normalizerCommaPointingObject p hS sat d X) :=
  F.normalizerAtChainCommaArrow _ d _ X _ (L.normalizerCommaPointingArrow p hS sat d X)

def normalizerCommaPointingHomEquiv
    (X : CostructuredArrow F.normalizerOrbitPairProjection d)
    (B : F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d)) :
    (L.normalizerCommaPointingObject p hS sat d X ⟶ B) ≃
      (X ⟶ (L.normalizerRepresentativeCommaInclusion p hS sat d).obj B) where
  toFun g := L.normalizerCommaPointingUnit p hS sat d X ≫
    (L.normalizerRepresentativeCommaInclusion p hS sat d).map g
  invFun f := ObjectProperty.homMk (Classical.choose
    (X.left.existsUnique_factorization (L.normalizerCommaPointingObject p hS sat d X) B
      (L.normalizerCommaPointingArrow p hS sat d X)
      (L.normalizerCommaPointingArrow_isIso p hS sat d X) f.left))
  left_inv g := by
    apply InducedCategory.hom_ext
    exact ((Classical.choose_spec
      (X.left.existsUnique_factorization (L.normalizerCommaPointingObject p hS sat d X) B
        (L.normalizerCommaPointingArrow p hS sat d X)
        (L.normalizerCommaPointingArrow_isIso p hS sat d X)
        (L.normalizerCommaPointingArrow p hS sat d X ≫ g.hom))).2 g.hom rfl).symm
  right_inv f := by
    apply CostructuredArrow.hom_ext
    exact (Classical.choose_spec
      (X.left.existsUnique_factorization (L.normalizerCommaPointingObject p hS sat d X) B
        (L.normalizerCommaPointingArrow p hS sat d X)
        (L.normalizerCommaPointingArrow_isIso p hS sat d X) f.left)).1

theorem normalizerCommaPointingHomEquiv_naturality
    (X : CostructuredArrow F.normalizerOrbitPairProjection d)
    (B B' : F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d))
    (g : B ⟶ B') (h : L.normalizerCommaPointingObject p hS sat d X ⟶ B) :
    L.normalizerCommaPointingHomEquiv p hS sat d X B' (h ≫ g) =
      L.normalizerCommaPointingHomEquiv p hS sat d X B h ≫
        (L.normalizerRepresentativeCommaInclusion p hS sat d).map g := by
  change L.normalizerCommaPointingUnit p hS sat d X ≫
    (L.normalizerRepresentativeCommaInclusion p hS sat d).map (h ≫ g) = _
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The actual reflection functor is determined by the universal pointing. -/
def normalizerOrbitCommaReflection :
    CostructuredArrow F.normalizerOrbitPairProjection d ⥤
      F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d) :=
  Adjunction.leftAdjointOfEquiv (L.normalizerCommaPointingHomEquiv p hS sat d)
    (L.normalizerCommaPointingHomEquiv_naturality p hS sat d)

def normalizerOrbitCommaReflectionAdjunction :
    L.normalizerOrbitCommaReflection p hS sat d ⊣ L.normalizerRepresentativeCommaInclusion p hS sat d :=
  Adjunction.adjunctionOfEquivLeft _ _

instance normalizerRepresentativeCommaInclusion_isRightAdjoint :
    (L.normalizerRepresentativeCommaInclusion p hS sat d).IsRightAdjoint :=
  ⟨_, ⟨L.normalizerOrbitCommaReflectionAdjunction p hS sat d⟩⟩

instance normalizerRepresentativeCommaInclusion_final :
    (L.normalizerRepresentativeCommaInclusion p hS sat d).Final :=
  Functor.final_of_adjunction (L.normalizerOrbitCommaReflectionAdjunction p hS sat d)

instance normalizerRepresentativeStructuredComma_initial :
    (F.normalizerAtChainToStructuredComma (L.normalizerSylowRepresentative p hS sat d) d
      (L.normalizerSylowRepresentative_class p hS sat d)).Initial := by
  infer_instance

/-- The relevant structured-arrow categories have actual initial objects,
not merely connected nerves. This retains the stronger universal property. -/
instance normalizerRepresentativeCommaInclusion_hasInitial
    (X : CostructuredArrow F.normalizerOrbitPairProjection d) :
    HasInitial (StructuredArrow X (L.normalizerRepresentativeCommaInclusion p hS sat d)) :=
  (mkInitialOfLeftAdjoint _ (L.normalizerOrbitCommaReflectionAdjunction p hS sat d) X).hasInitial

end Sharpness.FusionSystem.CentricLinkingSystem
