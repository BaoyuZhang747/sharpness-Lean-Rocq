import Sharpness.Unconditional.GroupCohomologyTransferHom

/-! Restriction and transfer between subgroup Hom complexes formed from one
fixed ambient complex. The maps use literal subgroup inclusions and the actual
finite-index transfer, with no prescribed cohomology or Mackey identities. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G]

/-- Restriction between two subgroups on their equivariant Hom spaces. -/
def subgroupHomRestriction (P Q : Subgroup G) (h : P ≤ Q) (X V : Rep.{u} R G) :
    (Rep.res Q.subtype X ⟶ Rep.res Q.subtype V) →ₗ[R]
      (Rep.res P.subtype X ⟶ Rep.res P.subtype V) :=
  (Rep.resFunctor (Subgroup.inclusion h)).mapLinearMap R

/-- The canonical change from the ambient subgroup type to its nested subgroup type. -/
def subgroupHomToNested (P Q : Subgroup G) (h : P ≤ Q) (X V : Rep.{u} R G) :
    (Rep.res P.subtype X ⟶ Rep.res P.subtype V) →ₗ[R]
      (Rep.res (P.subgroupOf Q).subtype (Rep.res Q.subtype X) ⟶
        Rep.res (P.subgroupOf Q).subtype (Rep.res Q.subtype V)) :=
  (Rep.resFunctor (Subgroup.subgroupOfEquivOfLe h).toMonoidHom).mapLinearMap R

/-- Actual finite-index transfer between subgroup Hom spaces. -/
def subgroupHomTransfer (P Q : Subgroup G) (h : P ≤ Q)
    [(P.subgroupOf Q).FiniteIndex] (X V : Rep.{u} R G) :
    (Rep.res P.subtype X ⟶ Rep.res P.subtype V) →ₗ[R]
      (Rep.res Q.subtype X ⟶ Rep.res Q.subtype V) :=
  (homTransfer (P.subgroupOf Q) (Rep.res Q.subtype X) (Rep.res Q.subtype V)).comp
    (subgroupHomToNested P Q h X V)

/-- Restriction on the common ambient Hom complex. -/
def subgroupHomComplexRestriction (P Q : Subgroup G) (h : P ≤ Q)
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    restrictedHomComplex Q X V ⟶ restrictedHomComplex P X V where
  f n := ModuleCat.ofHom (subgroupHomRestriction P Q h (X.X n) V)
  comm' i j _ := by
    ext f
    exact ((Rep.resFunctor (Subgroup.inclusion h)).map_comp
      ((Rep.resFunctor Q.subtype).map (X.d j i)) f).symm

/-- Transfer on the common ambient Hom complex. -/
def subgroupHomComplexTransfer (P Q : Subgroup G) (h : P ≤ Q)
    [(P.subgroupOf Q).FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    restrictedHomComplex P X V ⟶ restrictedHomComplex Q X V where
  f n := ModuleCat.ofHom (subgroupHomTransfer P Q h (X.X n) V)
  comm' i j _ := by
    ext f
    exact (homTransfer_precomp (P.subgroupOf Q)
      ((Rep.resFunctor Q.subtype).map (X.d j i))
      (subgroupHomToNested P Q h (X.X i) V f)).symm

end Sharpness.OrdinaryCohomology
