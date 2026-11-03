import Sharpness.FusionSystem
import Mathlib.CategoryTheory.SingleObj
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SingularSet

/-! The actual category underlying a centric linking system. Objects
are the actual F-centric subgroups of S; morphisms and their projection
to the raw fusion category are specified before passing to the orbit
category. This is category data, not a sharpness or decomposition input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

abbrev CentricSubgroup := {P : Subgroup S // F.IsCentric P}

def centricRawObject (P : F.CentricSubgroup) : F.Object := ⟨P.val⟩

structure LinkingCategoryData where
  Hom : F.CentricSubgroup → F.CentricSubgroup → Type u
  id : ∀ P, Hom P P
  comp : ∀ {P Q T}, Hom P Q → Hom Q T → Hom P T
  id_comp : ∀ {P Q} (f : Hom P Q), comp (id P) f = f
  comp_id : ∀ {P Q} (f : Hom P Q), comp f (id Q) = f
  assoc : ∀ {P Q T U} (f : Hom P Q) (g : Hom Q T) (h : Hom T U),
    comp (comp f g) h = comp f (comp g h)
  project : ∀ {P Q}, Hom P Q → (F.centricRawObject P ⟶ F.centricRawObject Q)
  project_id : ∀ P, project (id P) = 𝟙 (F.centricRawObject P)
  project_comp : ∀ {P Q T} (f : Hom P Q) (g : Hom Q T),
    project (comp f g) = project f ≫ project g

namespace LinkingCategoryData
variable {F} (L : F.LinkingCategoryData)

structure Object (_L : F.LinkingCategoryData) where
  as : F.CentricSubgroup

instance : Category.{u} L.Object where
  Hom P Q := L.Hom P.as Q.as
  id P := L.id P.as
  comp f g := L.comp f g
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc

def rawObject (P : L.Object) : F.Object := F.centricRawObject P.as

def projection : L.Object ⥤ F.Object where
  obj := L.rawObject
  map f := L.project f
  map_id P := L.project_id P.as
  map_comp f g := L.project_comp f g

def orbitProjection : L.Object ⥤ F.CentricOrbit where
  obj P := ⟨F.toOrbit.obj (L.rawObject P), P.as.property⟩
  map f := ObjectProperty.homMk (F.toOrbit.map (L.project f))
  map_id P := by
    apply ObjectProperty.hom_ext
    exact (congrArg F.toOrbit.map (L.project_id P.as)).trans (F.toOrbit.map_id _)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (congrArg F.toOrbit.map (L.project_comp f g)).trans (F.toOrbit.map_comp _ _)

/-- The geometric realization of the actual nerve of L. -/
def classifyingSpace : TopCat.{u} := SSet.toTop.obj (CategoryTheory.nerve L.Object)

end LinkingCategoryData
end Sharpness.FusionSystem
