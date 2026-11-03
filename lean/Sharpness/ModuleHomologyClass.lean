import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Concrete cycle classes in native module homology, together with
surjectivity and naturality for every actual short-complex morphism.
These formulas will identify connecting maps on actual representatives. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))

def moduleHomologyClass : ModuleCat.of R S.g.hom.ker ⟶ S.homology :=
  ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ ≫ S.moduleCatHomologyIso.inv

theorem moduleHomologyClass_cycles :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ = moduleHomologyClass S :=
  S.moduleCatCyclesIso_inv_π

theorem moduleHomologyClass_surjective : Function.Surjective (moduleHomologyClass S) := by
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective (S.moduleCatHomologyIso.hom y)
  exact ⟨x, (congrArg (fun t => S.moduleCatHomologyIso.inv t) hx).trans
    (S.moduleCatHomologyIso.toLinearEquiv.symm_apply_apply y)⟩

theorem moduleHomologyClass_epi : Epi (moduleHomologyClass S) :=
  (ModuleCat.epi_iff_surjective _).mpr (moduleHomologyClass_surjective S)

variable {S} {T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)

def moduleCycleMap : ModuleCat.of R S.g.hom.ker ⟶ ModuleCat.of R T.g.hom.ker :=
  ModuleCat.ofHom
    { toFun x := ⟨φ.τ₂ x.val, by
        have hc := congrArg (fun f => f x.val) φ.comm₂₃
        have hp : S.g x.val = 0 := x.property
        exact hc.trans ((congrArg (fun y => φ.τ₃ y) hp).trans φ.τ₃.hom.map_zero)⟩
      map_add' x y := Subtype.ext (φ.τ₂.hom.map_add x.val y.val)
      map_smul' r x := Subtype.ext (φ.τ₂.hom.map_smul r x.val) }

theorem moduleCycleMap_inclusion :
    moduleCycleMap φ ≫ ModuleCat.ofHom T.g.hom.ker.subtype =
      ModuleCat.ofHom S.g.hom.ker.subtype ≫ φ.τ₂ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem moduleCycleMap_cycles :
    S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ =
      moduleCycleMap φ ≫ T.moduleCatCyclesIso.inv := by
  apply (cancel_mono T.iCycles).mp
  simp only [Category.assoc, ShortComplex.cyclesMap_i,
    ShortComplex.moduleCatCyclesIso_inv_iCycles,
    ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem moduleHomologyClass_naturality :
    moduleHomologyClass S ≫ ShortComplex.homologyMap φ =
      moduleCycleMap φ ≫ moduleHomologyClass T := by
  calc
    _ = (S.moduleCatCyclesIso.inv ≫ S.homologyπ) ≫ ShortComplex.homologyMap φ :=
      congrArg (fun t => t ≫ ShortComplex.homologyMap φ) (moduleHomologyClass_cycles S).symm
    _ = S.moduleCatCyclesIso.inv ≫ (S.homologyπ ≫ ShortComplex.homologyMap φ) := Category.assoc _ _ _
    _ = S.moduleCatCyclesIso.inv ≫ (ShortComplex.cyclesMap φ ≫ T.homologyπ) :=
      congrArg (fun t => S.moduleCatCyclesIso.inv ≫ t) (ShortComplex.homologyπ_naturality φ)
    _ = (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ) ≫ T.homologyπ :=
      (Category.assoc _ _ _).symm
    _ = (moduleCycleMap φ ≫ T.moduleCatCyclesIso.inv) ≫ T.homologyπ :=
      congrArg (fun t => t ≫ T.homologyπ) (moduleCycleMap_cycles φ)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun t => moduleCycleMap φ ≫ t) (moduleHomologyClass_cycles T))

end Sharpness
