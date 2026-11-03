import Sharpness.CentricLinkingSystem
import Sharpness.CentralizerDefinitions
import Sharpness.CategoryRealizationHomotopyInput
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! The actual enlarged linking categories in BLO Theorem 2.6.
The label is a raw fusion map into P with a proved central image; the
companion labels module identifies this with Hom_F(E,Z(P)). Arrows retain
their actual linking-system morphisms. No sharpness premise is used. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

structure BLODiagramObject (E : F.Object) where
  point : L.Object
  label : E ⟶ L.projection.obj point
  central : ∀ e : E.subgroup, label.val e ∈ Subgroup.center point.as.val

abbrev BLODiagramHom {E : F.Object} (A B : L.BLODiagramObject E) :=
  {f : A.point ⟶ B.point // A.label ≫ L.projection.map f = B.label}

def BLODiagramIdentity {E : F.Object} (A : L.BLODiagramObject E) :
    L.BLODiagramHom A A :=
  ⟨𝟙 A.point, by rw [L.projection.map_id, Category.comp_id]⟩

def BLODiagramComposition {E : F.Object} {A B C : L.BLODiagramObject E}
    (f : L.BLODiagramHom A B) (g : L.BLODiagramHom B C) :
    L.BLODiagramHom A C :=
  ⟨f.val ≫ g.val, by rw [L.projection.map_comp, ← Category.assoc, f.property, g.property]⟩

instance BLODiagramCategory (E : F.Object) : Category.{u} (L.BLODiagramObject E) where
  Hom := L.BLODiagramHom
  id := L.BLODiagramIdentity
  comp f g := L.BLODiagramComposition f g
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

@[ext] theorem BLODiagramHom_ext {E : F.Object} {A B : L.BLODiagramObject E}
    (f g : A ⟶ B) (h : f.val = g.val) : f = g := Subtype.ext h

def BLODiagramForget (E : F.Object) : L.BLODiagramObject E ⥤ L.Object where
  obj A := A.point
  map f := f.val

@[simp] theorem BLODiagramForget_obj {E : F.Object} (A : L.BLODiagramObject E) :
    (L.BLODiagramForget E).obj A = A.point := rfl

@[simp] theorem BLODiagramForget_map {E : F.Object} {A B : L.BLODiagramObject E}
    (f : A ⟶ B) : (L.BLODiagramForget E).map f = f.val := rfl

instance BLODiagramForget_faithful (E : F.Object) : (L.BLODiagramForget E).Faithful where
  map_injective h := Subtype.ext h

def BLODiagramPrecomp {E E' : F.Object} (v : E ⟶ E') :
    L.BLODiagramObject E' ⥤ L.BLODiagramObject E where
  obj A := { point := A.point, label := v ≫ A.label, central := fun e => A.central (v.val e) }
  map f := ⟨f.val, by rw [Category.assoc, f.property]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem BLODiagramPrecomp_point {E E' : F.Object} (v : E ⟶ E')
    (A : L.BLODiagramObject E') : ((L.BLODiagramPrecomp v).obj A).point = A.point := rfl

@[simp] theorem BLODiagramPrecomp_label {E E' : F.Object} (v : E ⟶ E')
    (A : L.BLODiagramObject E') : ((L.BLODiagramPrecomp v).obj A).label = v ≫ A.label := rfl

@[simp] theorem BLODiagramPrecomp_map {E E' : F.Object} (v : E ⟶ E')
    {A B : L.BLODiagramObject E'} (f : A ⟶ B) :
    ((L.BLODiagramPrecomp v).map f).val = f.val := rfl

@[simp] theorem BLODiagramPrecomp_id (E : F.Object) :
    L.BLODiagramPrecomp (𝟙 E) = 𝟭 (L.BLODiagramObject E) := rfl

theorem BLODiagramPrecomp_comp {E E' E'' : F.Object} (v : E ⟶ E') (w : E' ⟶ E'') :
    L.BLODiagramPrecomp (v ≫ w) = L.BLODiagramPrecomp w ⋙ L.BLODiagramPrecomp v := rfl

@[simp] theorem BLODiagramPrecomp_forget {E E' : F.Object} (v : E ⟶ E') :
    L.BLODiagramPrecomp v ⋙ L.BLODiagramForget E = L.BLODiagramForget E' := rfl

variable [Finite S]

/-- The actual nerve-realisation diagram, with precisely the requested variance. -/
def BLODiagram (p : ℕ) : (F.ElementaryCategory p)ᵒᵖ ⥤ TopCat.{u} where
  obj E := categoryRealization (L.BLODiagramObject E.unop.obj)
  map v := categoryRealizationMap (L.BLODiagramPrecomp v.unop.hom)
  map_id E := by
    change categoryRealizationMap (L.BLODiagramPrecomp (𝟙 E.unop.obj)) = _
    rw [L.BLODiagramPrecomp_id, categoryRealizationMap_id]
  map_comp v w := by
    change categoryRealizationMap (L.BLODiagramPrecomp (w.unop.hom ≫ v.unop.hom)) = _
    rw [L.BLODiagramPrecomp_comp, categoryRealizationMap_comp]

/-- The forgetful augmentation has the actual nerve-realisation maps as legs. -/
def BLODiagramForgetfulCocone (p : ℕ) : Limits.Cocone (L.BLODiagram p) where
  pt := L.classifyingSpace
  ι :=
    { app := fun E => categoryRealizationMap (L.BLODiagramForget E.unop.obj)
      naturality := by
        intro E E' v
        change categoryRealizationMap (L.BLODiagramPrecomp v.unop.hom) ≫
          categoryRealizationMap (L.BLODiagramForget E'.unop.obj) =
          categoryRealizationMap (L.BLODiagramForget E.unop.obj) ≫ 𝟙 _
        rw [← categoryRealizationMap_comp, L.BLODiagramPrecomp_forget, Category.comp_id] }

theorem BLODiagramForgetfulCocone_app (p : ℕ) (E : F.ElementaryCategory p) :
    (L.BLODiagramForgetfulCocone p).ι.app (op E) =
      categoryRealizationMap (L.BLODiagramForget E.obj) := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
