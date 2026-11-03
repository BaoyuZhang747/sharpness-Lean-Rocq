import Sharpness.CategoryRealizationHomotopyInput
import Sharpness.Unconditional.RealizationNerveHomotopy
import Sharpness.Unconditional.GroupClassifyingComparison
import Sharpness.Unconditional.HeterogeneousNerve

/-! Native cohomology of actual realized categories.  The pullbacks below are
the homology maps of the singular cochain pullbacks.  Natural transformations
give equal pullbacks through the constructed nerve-realization homotopy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ)

def BLOCohomologyCategory (C : Type u) [Category.{u} C] : ModuleCat.{u} R :=
  SingularCohomology.cohomology R (categoryRealization C) A n

def BLOCohomologyPull {C D : Type u} [Category.{u} C] [Category.{u} D]
    (T : C ⥤ D) : BLOCohomologyCategory R A n D ⟶ BLOCohomologyCategory R A n C :=
  SingularCohomology.pull R (categoryRealizationMap T) A n

theorem BLOCohomologyPull_id (C : Type u) [Category.{u} C] :
    BLOCohomologyPull R A n (𝟭 C) = 𝟙 _ := by
  rw [BLOCohomologyPull, categoryRealizationMap_id, SingularCohomology.pull_id]
  rfl

theorem BLOCohomologyPull_comp {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E] (T : C ⥤ D) (U : D ⥤ E) :
    BLOCohomologyPull R A n (T ⋙ U) =
      BLOCohomologyPull R A n U ≫ BLOCohomologyPull R A n T := by
  rw [BLOCohomologyPull, categoryRealizationMap_comp, SingularCohomology.pull_comp]
  rfl

theorem BLOCohomologyPull_eq_of_natTrans {C D : Type u}
    [Category.{u} C] [Category.{u} D] {T U : C ⥤ D} (α : T ⟶ U) :
    BLOCohomologyPull R A n T = BLOCohomologyPull R A n U :=
  SingularCohomology.pull_eq_of_homotopy R (nerveRealizationHomotopy α) A n

def BLOCohomologyEquivalenceIso {C D : Type u}
    [Category.{u} C] [Category.{u} D] (e : C ≌ D) :
    BLOCohomologyCategory R A n D ≅ BLOCohomologyCategory R A n C where
  hom := BLOCohomologyPull R A n e.functor
  inv := BLOCohomologyPull R A n e.inverse
  hom_inv_id := by
    rw [← BLOCohomologyPull_comp]
    exact (BLOCohomologyPull_eq_of_natTrans R A n e.counitIso.hom).trans
      (BLOCohomologyPull_id R A n D)
  inv_hom_id := by
    rw [← BLOCohomologyPull_comp]
    exact (BLOCohomologyPull_eq_of_natTrans R A n e.unitIso.inv).trans
      (BLOCohomologyPull_id R A n C)

def BLOCohomologyGroupRestriction {C : Type u} [Category.{u} C]
    (G : Type u) [Group G] (i : SingleObj G ⥤ C) :
    BLOCohomologyCategory R A n C ⟶ OrdinaryCohomology.value R G A n :=
  SingularCohomology.pull R (SSet.toTop.map (nerveMapSingleObj G i)) A n ≫
    (OrdinaryCohomology.groupClassifyingCohomologyIso R G A n).hom

theorem BLOCohomologyGroupRestriction_precomp {C D : Type u}
    [Category.{u} C] [Category.{u} D] (G : Type u) [Group G]
    (i : SingleObj G ⥤ C) (T : C ⥤ D) :
    BLOCohomologyPull R A n T ≫ BLOCohomologyGroupRestriction R A n G i =
      BLOCohomologyGroupRestriction R A n G (i ⋙ T) := by
  unfold BLOCohomologyGroupRestriction BLOCohomologyPull
  rw [nerveMapSingleObj_comp, SSet.toTop.map_comp, SingularCohomology.pull_comp,
    Category.assoc]
  rfl

theorem BLOCohomologyGroupRestriction_group {C : Type u} [Category.{u} C]
    {G H : Type u} [Group G] [Group H] (f : G →* H) (j : SingleObj H ⥤ C) :
    BLOCohomologyGroupRestriction R A n G (f.toFunctor ⋙ j) =
      BLOCohomologyGroupRestriction R A n H j ≫
        OrdinaryCohomology.pull (R := R) (A := A) f n := by
  unfold BLOCohomologyGroupRestriction
  have hcomp : nerveMapSingleObj G (f.toFunctor ⋙ j) =
      nerveMap f.toFunctor ≫ nerveMapSingleObj H j := rfl
  rw [hcomp, SSet.toTop.map_comp, SingularCohomology.pull_comp, Category.assoc]
  have h := OrdinaryCohomology.groupClassifyingCohomologyIso_group
    (R := R) (A := A) f n
  change SingularCohomology.pull R (SSet.toTop.map (nerveMapSingleObj H j)) A n ≫
      (SingularCohomology.pull R (OrdinaryCohomology.classifyingMap f) A n ≫ _) = _
  rw [h, ← Category.assoc]

theorem BLOCohomologyGroupRestriction_eq_of_natTrans {C : Type u} [Category.{u} C]
    {G : Type u} [Group G] {i j : SingleObj G ⥤ C} (α : i ⟶ j) :
    BLOCohomologyGroupRestriction R A n G i =
      BLOCohomologyGroupRestriction R A n G j := by
  unfold BLOCohomologyGroupRestriction
  have h := SingularCohomology.pull_eq_of_homotopy R
    (realizationHomotopy (heterogeneousNerveHomotopy α)) A n
  exact congrArg (fun t => t ≫
    (OrdinaryCohomology.groupClassifyingCohomologyIso R G A n).hom) h

theorem BLOCohomologyGroupRestriction_naturality {C D : Type u}
    [Category.{u} C] [Category.{u} D] {G H : Type u} [Group G] [Group H]
    (f : G →* H) (i : SingleObj G ⥤ C) (j : SingleObj H ⥤ D) (T : C ⥤ D)
    (α : i ⋙ T ⟶ f.toFunctor ⋙ j) :
    BLOCohomologyPull R A n T ≫ BLOCohomologyGroupRestriction R A n G i =
      BLOCohomologyGroupRestriction R A n H j ≫
        OrdinaryCohomology.pull (R := R) (A := A) f n := by
  rw [BLOCohomologyGroupRestriction_precomp,
    BLOCohomologyGroupRestriction_eq_of_natTrans R A n α,
    BLOCohomologyGroupRestriction_group]

end Sharpness
