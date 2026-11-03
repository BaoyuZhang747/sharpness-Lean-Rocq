import Sharpness.Unconditional.NormalizerHigherLimitComparisonRanLocal
import Sharpness.Unconditional.NormalizerOrbitProjectionCommaReflection

/-! The actual right Kan extension of native centric-orbit cohomology
along the pair projection is naturally the native normalizer diagram.
All comma initiality and local index hypotheses are constructed from the
actual saturated fusion/linking system and its Sylow representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (n : ℕ)

include p hS sat in
theorem normalizerNativeToRan_isIso : IsIso (L.normalizerNativeToRan k A n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  exact L.normalizerNativeToRan_app_isIso k A n p hS sat
    (L.normalizerSylowRepresentative p hS sat d.unop) d.unop
    (L.normalizerSylowRepresentative_class p hS sat d.unop)
    (L.normalizerRepresentativeIndexIsUnit p hS sat k d.unop)

/-- The comparison is natural on the actual normalizer quotient, with all
native subgroup restriction maps retained. -/
def normalizerRanNativeIso :
    F.normalizerOrbitPairProjection.op.ran.obj
      (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n) ≅
        L.normalizerOrdinaryDiagram k A n := by
  letI := L.normalizerNativeToRan_isIso p hS sat k A n
  exact (asIso (L.normalizerNativeToRan k A n)).symm

@[simp] theorem normalizerRanNativeIso_inv :
    (L.normalizerRanNativeIso p hS sat k A n).inv = L.normalizerNativeToRan k A n := rfl

/-- The counit at every actual pair is exactly restriction along its acting
subgroup homomorphism, following the native chain comparison. -/
@[reassoc] theorem normalizerRanNativeIso_inv_app_counit (X : F.NormalizerOrbitPair) :
    (L.normalizerRanNativeIso p hS sat k A n).inv.app (op (F.normalizerClass X.chain)) ≫
      (F.normalizerOrbitPairProjection.op.ranCounit.app
        (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)).app
        (op X) =
      (L.normalizerNativeChainIso k A X.chain n).hom ≫
        OrdinaryCohomology.pull (L.normalizerPairActingHom X) n := by
  change (NormalizerRan.transpose F.normalizerOrbitPairProjection.op
    (L.normalizerPairNativeRestriction k A n)).app
      (F.normalizerOrbitPairProjection.op.obj (op X)) ≫ _ = _
  rw [NormalizerRan.transpose_counit, L.normalizerPairNativeRestriction_app]

@[reassoc] theorem normalizerRanNativeIso_inv_projection (d : F.NormalizerCategory)
    (X : StructuredArrow (op d) F.normalizerOrbitPairProjection.op) :
    (L.normalizerRanNativeIso p hS sat k A n).inv.app (op d) ≫
      (F.normalizerOrbitPairProjection.op.ranObjObjIsoLimit
        (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)
        (op d)).hom ≫
      limit.π (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n) X =
      (L.normalizerOrdinaryDiagram k A n).map X.hom ≫
        (L.normalizerNativeChainIso k A X.right.unop.chain n).hom ≫
          OrdinaryCohomology.pull (L.normalizerPairActingHom X.right.unop) n :=
  L.normalizerNativeToRan_projection k A n d X

end Sharpness.FusionSystem.CentricLinkingSystem
