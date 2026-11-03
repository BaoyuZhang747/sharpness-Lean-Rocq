import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalStable
import Mathlib.CategoryTheory.Limits.Final

/-! Normalized native limit comparisons on the actual ambient normalizer
collection. Every inverse component is the literal restriction to that subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (σ : F.CentricChain) (hindex : IsUnit ((L.chainNormalizerToAut σ).range.index : R))

def normalizerCollectionLimitIso (n : ℕ) :
    limit (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n) ≅
      OrdinaryCohomology.value R (L.ChainAut σ) A n :=
  L.normalizerCollectionOrdinaryStableIso p hS sat σ n ≪≫
    (OrdinaryCohomology.finiteGroupFusionAlongCohomologyStableIso
      (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ) n hindex).symm

theorem normalizerCollectionLimitIso_hom_pull_top (n : ℕ) :
    (L.normalizerCollectionLimitIso (R := R) (A := A) p hS sat σ hindex n).hom ≫
      OrdinaryCohomology.pull ((L.chainNormalizerToAut σ).comp
        (⊤ : Subgroup σ.normalizerSubgroup).subtype) n =
      limit.π (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n)
        (op ⟨(L.chainNormalizerFusion σ).topOrbit, L.normalizerAmbientCollection_top p hS sat σ⟩) := by
  simp only [normalizerCollectionLimitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← OrdinaryCohomology.finiteGroupFusionAlongCohomologyStableIso_hom_subtype
    (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ) n hindex,
    Iso.inv_hom_id_assoc]
  exact L.normalizerCollectionOrdinaryStableIso_evaluation p hS sat σ n

theorem normalizerCollectionLimitIso_inv_top (n : ℕ) :
    (L.normalizerCollectionLimitIso (R := R) (A := A) p hS sat σ hindex n).inv ≫
      limit.π (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n)
        (op ⟨(L.chainNormalizerFusion σ).topOrbit, L.normalizerAmbientCollection_top p hS sat σ⟩) =
      OrdinaryCohomology.pull ((L.chainNormalizerToAut σ).comp
        (⊤ : Subgroup σ.normalizerSubgroup).subtype) n := by
  rw [← L.normalizerCollectionLimitIso_hom_pull_top p hS sat σ hindex n, Iso.inv_hom_id_assoc]

theorem normalizerCollectionLimitIso_inv_component (n : ℕ)
    (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    (L.normalizerCollectionLimitIso (R := R) (A := A) p hS sat σ hindex n).inv ≫
      limit.π (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n) (op P) =
      OrdinaryCohomology.pull ((L.chainNormalizerToAut σ).comp P.obj.as.subgroup.subtype) n := by
  let N := L.chainNormalizerFusion σ
  let D := L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n
  let a : P ⟶ (⟨N.topOrbit, L.normalizerAmbientCollection_top p hS sat σ⟩ :
      (L.normalizerAmbientCollection p hS sat σ).Orbit) := ⟨N.toTop P.obj⟩
  have hmap : D.map a.op = OrdinaryCohomology.pull (R := R) (A := A)
      (N.inclusion (show P.obj.as.subgroup ≤ ⊤ from le_top)).val n :=
    N.cohomologyOrbitCoefficient_map_raw n (N.inclusion le_top)
  rw [← limit.w D a.op, ← Category.assoc, L.normalizerCollectionLimitIso_inv_top,
    hmap, ← OrdinaryCohomology.pull_comp]
  rfl

def normalizerAmbientGroupHom (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    σ.normalizerAmbientSubgroup P.obj.as.subgroup →* L.ChainAut σ :=
  ((L.chainNormalizerToAut σ).comp P.obj.as.subgroup.subtype).comp
    (σ.normalizerAmbientEquiv P.obj.as.subgroup).symm.toMonoidHom

def normalizerAmbientLimitIso (n : ℕ) :
    limit (L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat σ n) ≅
      OrdinaryCohomology.value R (L.ChainAut σ) A n :=
  HasLimit.isoOfNatIso (L.normalizerAmbientCohomologyIso p hS sat σ n) ≪≫
    L.normalizerCollectionLimitIso p hS sat σ hindex n

theorem normalizerAmbientLimitIso_inv_component (n : ℕ)
    (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    (L.normalizerAmbientLimitIso (R := R) (A := A) p hS sat σ hindex n).inv ≫
      limit.π (L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat σ n) (op P) =
      OrdinaryCohomology.pull (L.normalizerAmbientGroupHom p hS sat σ P) n := by
  simp only [normalizerAmbientLimitIso, Iso.trans_inv, Category.assoc]
  rw [HasLimit.isoOfNatIso_inv_π, ← Category.assoc,
    L.normalizerCollectionLimitIso_inv_component]
  change OrdinaryCohomology.pull _ n ≫
    OrdinaryCohomology.pull (σ.normalizerAmbientEquiv P.obj.as.subgroup).symm.toMonoidHom n = _
  rw [← OrdinaryCohomology.pull_comp]
  rfl

theorem normalizerAmbientLimitIso_hom_pull (n : ℕ)
    (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    (L.normalizerAmbientLimitIso (R := R) (A := A) p hS sat σ hindex n).hom ≫
      OrdinaryCohomology.pull (L.normalizerAmbientGroupHom p hS sat σ P) n =
      limit.π (L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat σ n) (op P) := by
  rw [← L.normalizerAmbientLimitIso_inv_component p hS sat σ hindex n P, Iso.hom_inv_id_assoc]

end Sharpness.FusionSystem.CentricLinkingSystem

