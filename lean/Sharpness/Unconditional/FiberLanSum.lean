import Sharpness.Unconditional.FiberLan
import Mathlib.Algebra.Category.ModuleCat.Products

/-! The left Kan extension from a strict fiber is the direct sum over base
arrows of the values at their cartesian lifts. The comparison is natural in
the coefficient diagram and requires neither finite fibers nor finite rings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open DirectSum

variable (R : Type u) [CommRing R]

/-- The concrete direct sum of a discrete module diagram, with its componentwise
action on natural transformations. -/
def discreteModuleSumFunctor (ι : Type u) :
    (Discrete ι ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj D := ModuleCat.of R (⨁ i : ι, D.obj (Discrete.mk i))
  map α := ModuleCat.ofHom (DirectSum.lmap fun i => (α.app (Discrete.mk i)).hom)
  map_id D := by
    apply ModuleCat.hom_ext
    exact DirectSum.lmap_id
  map_comp α β := by
    apply ModuleCat.hom_ext
    exact DirectSum.lmap_comp _ _

/-- The categorical colimit of a discrete module diagram is its direct sum. -/
def discreteColimitSumIso {ι : Type u} [DecidableEq ι]
    (D : Discrete ι ⥤ ModuleCat.{u} R) :
    colimit D ≅ (discreteModuleSumFunctor R ι).obj D :=
  colim.mapIso (Discrete.natIsoFunctor (F := D)) ≪≫
    ModuleCat.coprodIsoDirectSum (fun i => D.obj (Discrete.mk i))

@[reassoc (attr := simp)]
theorem discreteColimitSumIso_ι {ι : Type u} [DecidableEq ι]
    (D : Discrete ι ⥤ ModuleCat.{u} R) (i : ι) :
    colimit.ι D (Discrete.mk i) ≫ (discreteColimitSumIso R D).hom =
      ModuleCat.ofHom (DirectSum.lof R ι (fun j => D.obj (Discrete.mk j)) i) := by
  classical
  simp only [discreteColimitSumIso, Iso.trans_hom, Functor.mapIso_hom,
    colim_map, ι_colimMap_assoc, Discrete.natIsoFunctor_hom_app,
    Category.id_comp]
  exact ModuleCat.ι_coprodIsoDirectSum_hom (fun j => D.obj (Discrete.mk j)) i

/-- The concrete direct-sum comparison is natural in the whole discrete diagram. -/
def discreteColimitSumNatIso (ι : Type u) :
    colim (J := Discrete ι) (C := ModuleCat.{u} R) ≅
      discreteModuleSumFunctor R ι := by
  classical
  exact NatIso.ofComponents (discreteColimitSumIso R) (by
    intro D E α
    apply colimit.hom_ext
    rintro ⟨i⟩
    simp only [colim_map, ι_colimMap_assoc, discreteColimitSumIso_ι_assoc,
      discreteColimitSumIso_ι]
    ext x
    exact (DirectSum.lmap_lof (fun j => (α.app (Discrete.mk j)).hom) i x).symm)

variable {A B : Type u} [Category.{u} A] [Category.{u} B]
    (p : A ⥤ B) [p.IsPreFibered] (b : B) (a : A)

/-- The diagram on the actual chosen cartesian lifts indexed by base arrows. -/
def fiberLanDiscreteCoefficients :
    (Fiber p b ⥤ ModuleCat.{u} R) ⥤
      (Discrete (b ⟶ p.obj a) ⥤ ModuleCat.{u} R) :=
  (whiskeringLeft (FiberLanComma p b a) (Fiber p b) (ModuleCat.{u} R)).obj
      (CostructuredArrow.proj Fiber.fiberInclusion a) ⋙
    (whiskeringLeft (Discrete (b ⟶ p.obj a)) (FiberLanComma p b a)
      (ModuleCat.{u} R)).obj (fiberLanTerminals p b a)

/-- The right side of the fiber left-Kan formula, including its action on
coefficient transformations. Its summand at `f` is the value at `f* a`. -/
def fiberLanSumFunctor : (Fiber p b ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  fiberLanDiscreteCoefficients R p b a ⋙
    discreteModuleSumFunctor R (b ⟶ p.obj a)

/-- The pointwise left Kan extension from a fiber, naturally in its coefficient
functor, is the direct sum over all arrows from the fiber's base object. -/
def fiberLanEvaluationSumIso :
    Fiber.fiberInclusion.lan ⋙ (evaluation A (ModuleCat.{u} R)).obj a ≅
      fiberLanSumFunctor R p b a :=
  (fiberLanColimitEvaluationIso R p b a).symm ≪≫
    (isoWhiskerLeft
      ((whiskeringLeft (FiberLanComma p b a) (Fiber p b) (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj Fiber.fiberInclusion a))
      (Functor.Final.colimIso (fiberLanTerminals p b a))).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft (fiberLanDiscreteCoefficients R p b a)
      (discreteColimitSumNatIso R (b ⟶ p.obj a))

/-- The explicit module-valued left-Kan direct-sum formula. -/
def fiberLanSumIso (D : Fiber p b ⥤ ModuleCat.{u} R) :
    (Fiber.fiberInclusion.lan.obj D).obj a ≅
      ModuleCat.of R (⨁ f : b ⟶ p.obj a,
        D.obj (fiberLanTerminalObj p b a (Discrete.mk f)).left) :=
  (fiberLanEvaluationSumIso R p b a).app D

/-- In the concrete direct-sum coordinates, coefficient naturality is the
componentwise direct sum of the coefficient transformation. -/
theorem fiberLanSumIso_naturality {D E : Fiber p b ⥤ ModuleCat.{u} R}
    (α : D ⟶ E) :
    (Fiber.fiberInclusion.lan.map α).app a ≫ (fiberLanSumIso R p b a E).hom =
      (fiberLanSumIso R p b a D).hom ≫
        ModuleCat.ofHom (DirectSum.lmap fun f : b ⟶ p.obj a =>
          (α.app (fiberLanTerminalObj p b a (Discrete.mk f)).left).hom) :=
  (fiberLanEvaluationSumIso R p b a).hom.naturality α

end Sharpness
