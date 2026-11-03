import Sharpness.Unconditional.PuigGrowth
import Sharpness.Unconditional.PuigSpanRigidity
import Sharpness.Unconditional.PuigProductClassification

/-! Puig's finite representable product decomposition for the actual
centric orbit category of a saturated fusion system. Every input of the
maximal-extension argument is proved from saturation in the imported files. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

local instance : Finite F.CentricOrbit :=
  Finite.of_injective (fun X : F.CentricOrbit => X.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance (X Y : F.CentricOrbit) : Finite (X ⟶ Y) :=
  Finite.of_injective (fun f : X ⟶ Y => f.hom)
    (fun _ _ h => InducedCategory.hom_ext h)

/-- The product of two centric representables is an actual finite
coproduct of centric representables, with its natural universal property. -/
def centricProductDecomposition (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (P Q : F.CentricOrbit) :
    ProductDecomposition P Q :=
  productDecompositionOfMaximalSpans P Q
    (PuigSpan.exists_maximal_extension (fun X : F.CentricOrbit => F.orbitOrder X.obj)
      (fun {X Y : F.CentricOrbit} (f : X ⟶ Y) => F.orbitOrder_mono f.hom)
      (fun f => F.puig_isIso_of_order_eq f))
    (PuigSpan.maximal_factor_alignment (fun X : F.CentricOrbit => F.orbitOrder X.obj)
      (Nat.card S) (fun X => X.obj.as.subgroup.card_le_card_group)
      (fun {X Y : F.CentricOrbit} (f : X ⟶ Y) => F.orbitOrder_mono f.hom)
      (fun f => F.puig_isIso_of_order_eq f)
      (fun f g => F.centric_growth_amalgamation p hS sat f g))
    (F.maximal_span_rigid p sat)

end Sharpness.FusionSystem
