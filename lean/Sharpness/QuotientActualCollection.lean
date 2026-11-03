import Sharpness.CollectionRestriction
import Sharpness.QuotientFaithful
import Sharpness.QuotientComparison

/-! Identifying the preimage-indexed source with the actual full orbit
subcategory on X. The resulting equivalence has the manuscript's actual
X as its source, not merely a renamed abstract category. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

def quotientLiftToCollection : F.QuotientCentricLiftOrbit hZ p hS sat I ⥤
    (F.quotientComparisonCollection p hS sat hZ I).Orbit where
  obj A := ⟨(F.quotientSourceInclusion (Z := Z)).obj A.obj,
    ⟨QuotientGroup.le_comap_mk' Z A.obj.as, by
      change I.system.IsCentric ((F.quotientPreimage Z A.obj.as).map (QuotientGroup.mk' Z))
      rw [F.quotientPreimage_image]
      exact A.property⟩⟩
  map f := ObjectProperty.homMk ((F.quotientSourceInclusion (Z := Z)).map f.hom)
  map_id A := by
    apply InducedCategory.hom_ext
    exact (F.quotientSourceInclusion (Z := Z)).map_id A.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (F.quotientSourceInclusion (Z := Z)).map_comp f.hom g.hom

instance quotientLiftToCollection_full : (F.quotientLiftToCollection hZ p hS sat I).Full where
  map_surjective := by
    intro A B f
    obtain ⟨g, hg⟩ := (F.quotientSourceInclusion (Z := Z)).map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply InducedCategory.hom_ext
    exact hg

instance quotientLiftToCollection_faithful : (F.quotientLiftToCollection hZ p hS sat I).Faithful where
  map_injective := by
    intro A B f g h
    apply InducedCategory.hom_ext
    exact (F.quotientSourceInclusion (Z := Z)).map_injective (congrArg (fun t => t.hom) h)

instance quotientLiftToCollection_essSurj : (F.quotientLiftToCollection hZ p hS sat I).EssSurj where
  mem_essImage := by
    rintro ⟨⟨⟨P⟩⟩, hP⟩
    let A : F.QuotientCentricLiftOrbit hZ p hS sat I :=
      ⟨⟨P.map (QuotientGroup.mk' Z)⟩, hP.2⟩
    refine ⟨A, ⟨eqToIso ?_⟩⟩
    apply ObjectProperty.FullSubcategory.ext
    change F.toOrbit.obj ⟨F.quotientPreimage Z (P.map (QuotientGroup.mk' Z))⟩ =
      F.toOrbit.obj ⟨P⟩
    rw [F.quotientPreimage_map hP.1]

instance quotientLiftToCollection_isEquivalence :
    (F.quotientLiftToCollection hZ p hS sat I).IsEquivalence where

def quotientActualCentricEquivalence :
    (F.quotientComparisonCollection p hS sat hZ I).Orbit ≌ I.system.CentricOrbit :=
  (F.quotientLiftToCollection hZ p hS sat I).asEquivalence.symm.trans
    (F.quotientCentricEquivalence hZ p hS sat I)

end Sharpness.FusionSystem
