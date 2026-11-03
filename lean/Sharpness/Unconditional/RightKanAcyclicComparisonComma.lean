import Sharpness.Unconditional.CommaKanExactTerminal
import Sharpness.Unconditional.FiberLan

/-! Restriction to the actual structured-arrow category preserves injectives
for every functor. The left Kan extension of that restriction is exact: its
pointwise comma category has a terminal representative for each base arrow. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

variable {A B : Type u} [Category.{u} A] [Category.{u} B]
    (r : A ⥤ B) (b : B) (a : A)

def structuredProjLanTerminal (f : b ⟶ r.obj a) :
    CostructuredArrow (StructuredArrow.proj b r) a :=
  CostructuredArrow.mk (Y := StructuredArrow.mk f) (𝟙 a)

@[reducible] def structuredProjLanTerminalUnique
    (X : CostructuredArrow (StructuredArrow.proj b r) a) :
    Unique (Σ f : b ⟶ r.obj a, X ⟶ structuredProjLanTerminal r b a f) where
  default := ⟨X.left.hom ≫ r.map X.hom,
    CostructuredArrow.homMk (StructuredArrow.homMk X.hom rfl)
      (by change X.hom ≫ 𝟙 a = X.hom; exact Category.comp_id _)⟩
  uniq y := by
    rcases y with ⟨f, h⟩
    have he : h.left.right = X.hom := by
      simpa [structuredProjLanTerminal] using CostructuredArrow.w h
    have hf : f = X.left.hom ≫ r.map X.hom := by
      simpa [structuredProjLanTerminal, he] using (StructuredArrow.w h.left).symm
    subst f
    congr 1
    apply CostructuredArrow.hom_ext
    apply StructuredArrow.hom_ext
    exact he

def structuredProjLanTerminals :
    Discrete (b ⟶ r.obj a) ⥤ CostructuredArrow (StructuredArrow.proj b r) a :=
  Discrete.functor (structuredProjLanTerminal r b a)

instance structuredProjLanTerminals_final : (structuredProjLanTerminals r b a).Final :=
  final_discrete_of_unique_terminal_family _ (structuredProjLanTerminalUnique r b a)

variable (R : Type u) [CommRing R]

instance structuredProjLanComma_hasExactColimits :
    HasExactColimitsOfShape (CostructuredArrow (StructuredArrow.proj b r) a)
      (ModuleCat.{u} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{u} R) (structuredProjLanTerminals r b a)

def structuredProjLanColimitEvaluationIso :
    (whiskeringLeft (CostructuredArrow (StructuredArrow.proj b r) a)
      (StructuredArrow b r) (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj (StructuredArrow.proj b r) a) ⋙ colim ≅
      (StructuredArrow.proj b r).lan ⋙ (evaluation A (ModuleCat.{u} R)).obj a :=
  NatIso.ofComponents
    (fun D => ((StructuredArrow.proj b r).leftKanExtensionObjIsoColimit D a).symm) (by
      intro D E α
      apply colimit.hom_ext
      intro X
      change colimit.ι _ X ≫ colimMap (Functor.whiskerLeft _ α) ≫
          ((StructuredArrow.proj b r).leftKanExtensionObjIsoColimit E a).inv =
        colimit.ι _ X ≫ ((StructuredArrow.proj b r).leftKanExtensionObjIsoColimit D a).inv ≫
          ((StructuredArrow.proj b r).lan.map α).app a
      simp only [ι_colimMap_assoc, Functor.whiskerLeft_app,
        Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc,
        Functor.ι_leftKanExtensionObjIsoColimit_inv]
      change α.app X.left ≫ ((StructuredArrow.proj b r).lanUnit.app E).app X.left ≫
          ((StructuredArrow.proj b r).lan.obj E).map X.hom =
        ((StructuredArrow.proj b r).lanUnit.app D).app X.left ≫
          ((StructuredArrow.proj b r).lan.obj D).map X.hom ≫
            ((StructuredArrow.proj b r).lan.map α).app a
      rw [((StructuredArrow.proj b r).lan.map α).naturality X.hom]
      simp only [← Category.assoc]
      congr 1
      exact congr_app ((StructuredArrow.proj b r).lanUnit.naturality α) X.left)

instance structuredProjLan_preservesFiniteLimits :
    PreservesFiniteLimits ((StructuredArrow.proj b r).lan :
      (StructuredArrow b r ⥤ ModuleCat.{u} R) ⥤ (A ⥤ ModuleCat.{u} R)) := by
  apply preservesFiniteLimits_of_evaluation
  intro a
  letI : PreservesFiniteLimits
      ((whiskeringLeft (CostructuredArrow (StructuredArrow.proj b r) a)
        (StructuredArrow b r) (ModuleCat.{u} R)).obj
          (CostructuredArrow.proj (StructuredArrow.proj b r) a)) := ⟨fun _ => inferInstance⟩
  exact preservesFiniteLimits_of_natIso (structuredProjLanColimitEvaluationIso r b a R)

instance structuredProjRestriction_preservesInjectiveObjects :
    ((whiskeringLeft (StructuredArrow b r) A (ModuleCat.{u} R)).obj
      (StructuredArrow.proj b r)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((StructuredArrow.proj b r).lanAdjunction (ModuleCat.{u} R))

end Sharpness
