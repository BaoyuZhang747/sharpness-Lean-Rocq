import Sharpness.Unconditional.NormalizerHigherLimitComparisonRanFramework
import Sharpness.Unconditional.NormalizerHigherLimitComparisonRanCone
import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalPairLimitMaps
import Sharpness.Unconditional.NormalizerOrbitProjectionCommaOpposite

/-! The native normalizer diagram maps naturally to the actual right Kan
extension. Its restriction to a literal fixed-chain comma model agrees
with the already normalized local limit comparison, component by component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ)

def normalizerNativeToRan :
    L.normalizerOrdinaryDiagram R A n ⟶
      F.normalizerOrbitPairProjection.op.ran.obj
        (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n) :=
  NormalizerRan.transpose F.normalizerOrbitPairProjection.op
    (L.normalizerPairNativeRestriction R A n)

@[reassoc] theorem normalizerNativeToRan_projection (d : F.NormalizerCategory)
    (X : StructuredArrow (op d) F.normalizerOrbitPairProjection.op) :
    (L.normalizerNativeToRan R A n).app (op d) ≫
      (F.normalizerOrbitPairProjection.op.ranObjObjIsoLimit
        (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n)
        (op d)).hom ≫
      limit.π (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n) X =
      (L.normalizerOrdinaryDiagram R A n).map X.hom ≫
        (L.normalizerNativeChainIso R A X.right.unop.chain n).hom ≫
          OrdinaryCohomology.pull (L.normalizerPairActingHom X.right.unop) n := by
  rw [show (L.normalizerNativeToRan R A n).app (op d) =
    (NormalizerRan.transpose F.normalizerOrbitPairProjection.op
      (L.normalizerPairNativeRestriction R A n)).app (op d) from rfl,
    NormalizerRan.transpose_projection, L.normalizerPairNativeRestriction_app]

def normalizerNativeAtClassIso (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) :
    (L.normalizerOrdinaryDiagram R A n).obj (op d) ≅
      OrdinaryCohomology.value R (L.ChainAut σ) A n :=
  (L.normalizerOrdinaryDiagram R A n).mapIso (eqToIso hσ).op ≪≫
    L.normalizerNativeChainIso R A σ n

theorem normalizerPairNativeRestriction_atChain (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    (P : F.NormalizerOrbitAtChain σ) :
    (L.normalizerOrdinaryDiagram R A n).map
        ((F.normalizerAtChainToStructuredComma σ d hσ).obj (op P)).hom ≫
        (L.normalizerPairNativeRestriction R A n).app (op P.obj) =
      (L.normalizerNativeAtClassIso R A n σ d hσ).hom ≫
        OrdinaryCohomology.pull (L.normalizerAtChainGroupHom σ P) n := by
  subst d
  rcases P with ⟨P,hP⟩
  change P.chain = σ at hP
  subst σ
  rw [L.normalizerPairNativeRestriction_app]
  change (L.normalizerOrdinaryDiagram R A n).map (𝟙 _) ≫ _ =
    ((L.normalizerOrdinaryDiagram R A n).map (𝟙 _) ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

def normalizerRanToLocalLimit (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) :
    (F.normalizerOrbitPairProjection.op.ran.obj
      (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n)).obj (op d) ⟶
        limit (F.normalizerAtChainCohomologyCoefficient R A σ n) :=
  (F.normalizerOrbitPairProjection.op.ranObjObjIsoLimit
    (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n)
    (op d)).hom ≫
    limit.pre (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
      F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n)
      (F.normalizerAtChainToStructuredComma σ d hσ)

@[reassoc] theorem normalizerNativeToRan_local_projection (σ : F.CentricChain)
    (d : F.NormalizerCategory) (hσ : F.normalizerClass σ = d)
    (P : F.NormalizerOrbitAtChain σ) :
    (L.normalizerNativeToRan R A n).app (op d) ≫
      normalizerRanToLocalLimit (F := F) R A n σ d hσ ≫
        limit.π (F.normalizerAtChainCohomologyCoefficient R A σ n) (op P) =
      (L.normalizerNativeAtClassIso R A n σ d hσ).hom ≫
        OrdinaryCohomology.pull (L.normalizerAtChainGroupHom σ P) n := by
  let D := StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
    F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n
  let J := F.normalizerAtChainToStructuredComma σ d hσ
  let e := F.normalizerOrbitPairProjection.op.ranObjObjIsoLimit
    (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n) (op d)
  have hπ : normalizerRanToLocalLimit R A n σ d hσ ≫
      limit.π (F.normalizerAtChainCohomologyCoefficient R A σ n) (op P) =
        e.hom ≫ limit.π D (J.obj (op P)) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun g => e.hom ≫ g) (limit.pre_π D J (op P)))
  calc
    _ = (L.normalizerNativeToRan R A n).app (op d) ≫
        e.hom ≫ limit.π D (J.obj (op P)) :=
      congrArg (fun g => (L.normalizerNativeToRan R A n).app (op d) ≫ g) hπ
    _ = (L.normalizerOrdinaryDiagram R A n).map (J.obj (op P)).hom ≫
        (L.normalizerPairNativeRestriction R A n).app (op P.obj) :=
      NormalizerRan.transpose_projection F.normalizerOrbitPairProjection.op
        (L.normalizerPairNativeRestriction R A n) (op d) (J.obj (op P))
    _ = _ := L.normalizerPairNativeRestriction_atChain R A n σ d hσ P

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

theorem normalizerNativeToRan_local (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) (hindex : IsUnit ((L.chainNormalizerToAut σ).range.index : R)) :
    (L.normalizerNativeToRan R A n).app (op d) ≫
      normalizerRanToLocalLimit (F := F) R A n σ d hσ =
      (L.normalizerNativeAtClassIso R A n σ d hσ).hom ≫
        (L.normalizerAtChainLimitIso (R := R) (A := A) p hS sat σ hindex n).inv := by
  apply limit.hom_ext
  intro P
  simp only [Category.assoc]
  rw [L.normalizerAtChainLimitIso_inv_component p hS sat σ hindex n P.unop]
  exact L.normalizerNativeToRan_local_projection R A n σ d hσ P.unop

instance normalizerRanToLocalLimit_isIso (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d)
    [(F.normalizerAtChainToStructuredComma σ d hσ).Initial] :
    IsIso (normalizerRanToLocalLimit (F := F) R A n σ d hσ) := by
  dsimp only [normalizerRanToLocalLimit]
  infer_instance

include p hS sat in
theorem normalizerNativeToRan_app_isIso (σ : F.CentricChain) (d : F.NormalizerCategory)
    (hσ : F.normalizerClass σ = d) (hindex : IsUnit ((L.chainNormalizerToAut σ).range.index : R))
    [(F.normalizerAtChainToStructuredComma σ d hσ).Initial] :
    IsIso ((L.normalizerNativeToRan R A n).app (op d)) := by
  have h := L.normalizerNativeToRan_local R A n p hS sat σ d hσ hindex
  haveI : IsIso ((L.normalizerNativeToRan R A n).app (op d) ≫
      normalizerRanToLocalLimit (F := F) R A n σ d hσ) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (normalizerRanToLocalLimit (F := F) R A n σ d hσ)

end Sharpness.FusionSystem.CentricLinkingSystem


