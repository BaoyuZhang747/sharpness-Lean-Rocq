import Sharpness.Unconditional.PuigNormalization
import Sharpness.Unconditional.PuigMaximalRigidity

/-! Rigidity of arbitrary maximal centric spans, obtained by normalizing
their first projection to an actual subgroup inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- A maximal centric span has no nonidentity endomorphism preserving both
projections. The normalization and saturation arguments are explicit. -/
theorem maximal_span_rigid (p : ℕ) (sat : F.Saturated p)
    {P Q : F.CentricOrbit} (A : PuigSpan P Q) (hmax : A.Maximal)
    (f : A.Factor A) : f.hom = 𝟙 A.apex := by
  obtain ⟨H, hH, hHP, e, he⟩ := F.normalize_centric_arrow A.left
  let B : PuigSpan P Q :=
    { apex := F.puigObject H hH
      left := F.puigInclusion hHP
      right := e.inv ≫ A.right }
  let t : A.Factor B :=
    { hom := e.hom
      left_fac := he
      right_fac := by simp [B] }
  let s : B.Factor A :=
    { hom := e.inv
      left_fac := by rw [← he]; simp [B]
      right_fac := rfl }
  have hB : B.Maximal := by
    intro C k
    haveI : IsIso (e.hom ≫ k.hom) := hmax C (t.comp k)
    have heq : k.hom = e.inv ≫ (e.hom ≫ k.hom) := by simp
    rw [heq]
    infer_instance
  let k : B.Factor B := (s.comp f).comp t
  letI : IsIso k.hom := hB B k
  let inc : F.CentricOrbit ⥤ F.Orbit :=
    ObjectProperty.ι (fun P : F.Orbit => F.IsCentric P.as.subgroup)
  let a : Aut (F.toOrbit.obj ⟨H⟩) := inc.mapIso (asIso k.hom)
  have ha : a = 1 := F.maximal_normalized_span_aut_eq_one p sat hH hHP
    (e.inv ≫ A.right).hom hB a
    (by simpa only [a, inc] using!
      congrArg (fun h : B.apex ⟶ P => h.hom) k.left_fac)
    (by simpa only [a, inc] using!
      congrArg (fun h : B.apex ⟶ Q => h.hom) k.right_fac)
  have hk : k.hom = 𝟙 B.apex := by
    apply InducedCategory.hom_ext
    exact congrArg Iso.hom ha
  have hh := congrArg (fun h : B.apex ⟶ B.apex => e.hom ≫ h ≫ e.inv) hk
  simpa [k, s, t, B, PuigSpan.Factor.comp, Category.assoc] using hh

end Sharpness.FusionSystem
