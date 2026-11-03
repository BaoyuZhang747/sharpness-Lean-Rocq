import Sharpness.QuotientCollection
import Sharpness.PrimeLocalRing

/-! The precise general Yalcin Proposition 10.5 input, applied only after
proving the comparison collection's hypotheses. The ground ring is the
actual Z_(p). No central quotient comparison is a field of the input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime]

structure ComparisonCollection where
  member : Subgroup S → Prop
  centric : ∀ P, member P → F.IsCentric P
  overgroup : ∀ {P Q}, member P → P ≤ Q → member Q
  contains_centric_radical : ∀ P, F.IsCentric P → F.IsRadical p P → member P

namespace ComparisonCollection
variable {F p} (C : F.ComparisonCollection p)

abbrev Orbit := ObjectProperty.FullSubcategory (fun P : F.Orbit => C.member P.as.subgroup)

def toCentric : C.Orbit ⥤ F.CentricOrbit where
  obj P := ⟨P.obj, C.centric _ P.property⟩
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end ComparisonCollection

variable (hS : IsPGroup p S) (sat : F.Saturated p)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit)]

/-- Published Proposition 10.5 for every eligible collection and every
Z_(p)-valued coefficient. This does not select the manuscript's X. -/
structure YalcinRestrictionInput (hS : IsPGroup p S) (sat : F.Saturated p) where
  proposition_10_5 : ∀ (C : F.ComparisonCollection p)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) C.Orbit)]
    (D : CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit) (i : ℕ),
    higherLimit (C.toCentric.op ⋙ D) i ≅ higherLimit D i

variable {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

def quotientComparisonCollection : F.ComparisonCollection p where
  member := F.quotientCollection hZ p hS sat I
  centric _ := F.quotientCollection_centric hZ p hS sat I
  overgroup := F.quotientCollection_overgroup hZ p hS sat I
  contains_centric_radical _ := F.centric_radical_in_quotientCollection hZ p hS sat I

def quotientCollectionHigherLimitIso
    (Y : F.YalcinRestrictionInput p hS sat)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p)
      (F.quotientComparisonCollection p hS sat hZ I).Orbit)]
    (D : CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit) (i : ℕ) :
    higherLimit ((F.quotientComparisonCollection p hS sat hZ I).toCentric.op ⋙ D) i ≅
      higherLimit D i :=
  Y.proposition_10_5 (F.quotientComparisonCollection p hS sat hZ I) D i

end Sharpness.FusionSystem
