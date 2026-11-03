import Sharpness.SingularCochainFunctor
import Sharpness.Unconditional.ElementaryReplacementLimitEdge

/-! The actual singular-cochain augmentation associated to a topological
cocone. Its zero-column edge is the family of pullbacks along the cocone.
These general lemmas are later specialized to the actual BLO diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.BLOEdge
open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{u} C] (D : C ⥤ TopCat.{u})
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def cochainDiagram : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  D.op ⋙ SingularCohomology.cochainFunctor R A

def cohomologyDiagram (n : ℕ) : Cᵒᵖ ⥤ ModuleCat.{u} R :=
  replacementCohomologyDiagram (cochainDiagram D R A) n

def totalCochains : CochainComplex (ModuleCat.{u} R) ℕ :=
  cochainReplacementTotal (cochainDiagram D R A)

variable (a : Cocone D)

def restrictionCone (n : ℕ) : Cone (cohomologyDiagram D R A n) where
  pt := SingularCohomology.cohomology R a.pt A n
  π :=
    { app X := SingularCohomology.pull R (a.ι.app X.unop) A n
      naturality {X Y} f := by
        change (𝟙 _) ≫ SingularCohomology.pull R (a.ι.app Y.unop) A n =
          SingularCohomology.pull R (a.ι.app X.unop) A n ≫
            SingularCohomology.pull R (D.map f.unop) A n
        rw [Category.id_comp, ← SingularCohomology.pull_comp, a.w f.unop] }

def restrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology R a.pt A n ⟶ limit (cohomologyDiagram D R A n) :=
  limit.lift _ (restrictionCone D R A a n)

@[reassoc] theorem restrictionToLimit_component (n : ℕ) (X : C) :
    restrictionToLimit D R A a n ≫ limit.π (cohomologyDiagram D R A n) (op X) =
      SingularCohomology.pull R (a.ι.app X) A n :=
  limit.lift_π _ _

def cochainRestrictionCone :
    (Functor.const Cᵒᵖ).obj (SingularCohomology.cochains R a.pt A) ⟶
      cochainDiagram D R A where
  app X := SingularCohomology.cochainPull R (a.ι.app X.unop) A
  naturality {X Y} f := by
    change (𝟙 _) ≫ SingularCohomology.cochainPull R (a.ι.app Y.unop) A =
      SingularCohomology.cochainPull R (a.ι.app X.unop) A ≫
        SingularCohomology.cochainPull R (D.map f.unop) A
    rw [Category.id_comp, ← SingularCohomology.cochainPull_comp, a.w f.unop]

def cochainAugmentation :
    SingularCohomology.cochains R a.pt A ⟶ totalCochains D R A :=
  replacementConeAugmentation (cochainDiagram D R A) (cochainRestrictionCone D R A a)

def totalProjection (X : C) :
    totalCochains D R A ⟶ SingularCohomology.cochains R (D.obj X) A :=
  replacementTotalProjection (cochainDiagram D R A) (ComposableArrows.mk₀ X)

@[reassoc] theorem cochainAugmentation_projection (X : C) :
    cochainAugmentation D R A a ≫ totalProjection D R A X =
      SingularCohomology.cochainPull R (a.ι.app X) A :=
  replacementConeAugmentation_comp_projection (cochainDiagram D R A)
    (cochainRestrictionCone D R A a) (ComposableArrows.mk₀ X)

@[reassoc] theorem cochainAugmentation_homology_component (n : ℕ) (X : C) :
    HomologicalComplex.homologyMap (cochainAugmentation D R A a) n ≫
        HomologicalComplex.homologyMap (totalProjection D R A X) n =
      SingularCohomology.pull R (a.ι.app X) A n := by
  rw [← HomologicalComplex.homologyMap_comp, cochainAugmentation_projection]
  rfl

theorem restrictionToLimit_eq_edge (n : ℕ) :
    restrictionToLimit D R A a n =
      HomologicalComplex.homologyMap (cochainAugmentation D R A a) n ≫
        elementaryReplacementLimitEdge (cochainDiagram D R A) n := by
  apply limit.hom_ext
  intro X
  rw [Category.assoc]
  rw [show elementaryReplacementLimitEdge (cochainDiagram D R A) n ≫
      limit.π (cohomologyDiagram D R A n) X = _ from
    elementaryReplacementLimitEdge_component (cochainDiagram D R A) n X.unop]
  exact (restrictionToLimit_component D R A a n X.unop).trans
    (cochainAugmentation_homology_component D R A a n X.unop).symm

theorem cochainAugmentation_quasiIso_of_canonical_restriction
    (hpos : ∀ q s : ℕ, IsZero (higherLimit (cohomologyDiagram D R A q) (s + 1)))
    (hres : ∀ n : ℕ, IsIso (restrictionToLimit D R A a n)) :
    QuasiIso (cochainAugmentation D R A a) := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  letI := elementaryReplacementLimitEdge_isIso (cochainDiagram D R A) hpos n
  apply (isIso_comp_right_iff _ (elementaryReplacementLimitEdge (cochainDiagram D R A) n)).mp
  rw [← restrictionToLimit_eq_edge]
  exact hres n

end Sharpness.BLOEdge
