import Sharpness.FusionMackey
import Sharpness.Limits
import Mathlib.CategoryTheory.Abelian.Ext

/-!
Higher limits as Ext from the constant coefficient functor, the standard
description used in AKO III.5.3. The ambient enough-projectives instances
are constructed in `Unconditional.ProjectiveCoefficients`.

This uses Mathlib's actual Ext construction, rather than an uninterpreted
predicate named "vanishing".
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

abbrev CoefficientCategory (R : Type u) [Ring R] (C : Type u) [Category.{u} C] :=
  Cᵒᵖ ⥤ ModuleCat.{u} R

def constantCoefficient (R : Type u) [Ring R] (C : Type u) [Category.{u} C] :
    CoefficientCategory R C := (Functor.const Cᵒᵖ).obj (ModuleCat.of R R)

def higherLimit {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)]
    (D : CoefficientCategory R C) (i : ℕ) : ModuleCat.{u} R :=
  ((Ext R (CoefficientCategory R C) i).obj (op (constantCoefficient R C))).obj D

def Acyclic {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)] (D : CoefficientCategory R C) : Prop :=
  ∀ i : ℕ, 0 < i → IsZero (higherLimit D i)

def higherLimitIso {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)]
    {D E : CoefficientCategory R C} (e : D ≅ E) (i : ℕ) :
    higherLimit D i ≅ higherLimit E i :=
  ((Ext R (CoefficientCategory R C) i).obj (op (constantCoefficient R C))).mapIso e

theorem acyclic_of_iso {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)]
    {D E : CoefficientCategory R C} (e : D ≅ E) (h : Acyclic E) : Acyclic D := by
  intro i hi
  exact IsZero.of_iso (h i hi) (higherLimitIso e i)

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]

def coefficientData (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    Coefficient R F.Orbit where
  Value := M.Value
  valueAddCommGroup := M.valueAddCommGroup
  valueModule := M.valueModule
  pull := M.pull
  pull_id := M.pull_id
  pull_comp := M.pull_comp

def coefficient (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    CoefficientCategory R F.Orbit where
  obj P := ModuleCat.of R (M.Value P.unop)
  map f := ModuleCat.ofHom (M.pull f.unop)
  map_id P := by
    apply ModuleCat.hom_ext
    exact M.pull_id P.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact M.pull_comp g.unop f.unop

def centricInclusion : F.CentricOrbit ⥤ F.Orbit :=
  ObjectProperty.ι (fun P : F.Orbit => F.IsCentric P.as.subgroup)

def centricCoefficient (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    CoefficientCategory R F.CentricOrbit := F.centricInclusion.op ⋙ F.coefficient M

def Sharp [EnoughProjectives (CoefficientCategory R F.CentricOrbit)] : Prop :=
  ∀ M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape, Acyclic (F.centricCoefficient M)

end FusionSystem
end Sharpness
