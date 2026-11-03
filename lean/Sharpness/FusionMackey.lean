import Sharpness.FusionSystem
import Sharpness.NormalForms
import Mathlib.GroupTheory.DoubleCoset

/-!
The concrete full Mackey formula on the fusion orbit category.
Every term is indexed by an actual double coset of image subgroups in the
target group. The apex is an actual intersection/preimage subgroup of S.
No vanishing conclusion is part of this construction.
-/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def imageSubgroup {P Q : F.Object} (f : P ⟶ Q) : Subgroup S :=
  (Q.subgroup.subtype.comp f.val).range

theorem image_le {P Q : F.Object} (f : P ⟶ Q) : F.imageSubgroup f ≤ Q.subgroup := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact (f.val y).property

def toImage {P Q : F.Object} (f : P ⟶ Q) : P ⟶ ⟨F.imageSubgroup f⟩ := by
  let g := (Q.subgroup.subtype.comp f.val).rangeRestrict
  refine ⟨g, F.codomain_restrict_mem f.val f.property (F.image_le f) g ?_⟩
  ext x
  rfl

theorem image_factorization {P Q : F.Object} (f : P ⟶ Q) :
    F.toImage f ≫ F.inclusion (F.image_le f) = f := by
  apply Subtype.ext
  ext x
  rfl

def imageIso {P Q : F.Object} (f : P ⟶ Q) : P ≅ (⟨F.imageSubgroup f⟩ : F.Object) := by
  have hinj : Function.Injective (Q.subgroup.subtype.comp f.val) :=
    Subtype.val_injective.comp (F.injective _ f.property)
  let e := MonoidHom.ofInjective hinj
  exact
    { hom := F.toImage f
      inv := ⟨e.symm.toMonoidHom, F.inverse_mem e (F.toImage f).property⟩
      hom_inv_id := by
        apply Subtype.ext
        ext x
        exact congrArg Subtype.val (e.symm_apply_apply x)
      inv_hom_id := by
        apply Subtype.ext
        ext x
        exact congrArg Subtype.val (e.apply_symm_apply x) }

def conjugateEnd (T : F.Object) (u : T.subgroup) : T ⟶ T :=
  ⟨subgroupConjugation T.subgroup T.subgroup u.val
    (fun _x hx => T.subgroup.mul_mem (T.subgroup.mul_mem (T.subgroup.inv_mem u.property) hx) u.property),
    F.conjugation_mem _ _ _ _⟩

theorem lifted_le (P : Subgroup S) (A : Subgroup P) : A.map P.subtype ≤ P := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

theorem lifted_mem (P : Subgroup S) (A : Subgroup P) (x : A.map P.subtype) :
    (⟨x.val, lifted_le P A x.property⟩ : P) ∈ A := by
  obtain ⟨y, hy, he⟩ := x.property
  have hyx : y = (⟨x.val, lifted_le P A x.property⟩ : P) := Subtype.ext he
  exact hyx ▸ hy

def spanInternal {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) :
    Subgroup P.subgroup := g.val.range.comap ((F.conjugateEnd T u).val.comp f.val)

def spanApex {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) : F.Object :=
  ⟨(F.spanInternal f g u).map P.subgroup.subtype⟩

def spanLeft {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) :
    F.spanApex f g u ⟶ P := F.inclusion (lifted_le _ _)

def spanConjugate {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) :
    F.spanApex f g u ⟶ T := F.spanLeft f g u ≫ f ≫ F.conjugateEnd T u

theorem spanConjugate_mem_range {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (u : T.subgroup) (x : (F.spanApex f g u).subgroup) :
    (F.spanConjugate f g u).val x ∈ g.val.range := by
  exact lifted_mem P.subgroup (F.spanInternal f g u) x

def spanToImage {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) :
    F.spanApex f g u ⟶ (⟨F.imageSubgroup g⟩ : F.Object) := by
  let h := F.spanConjugate f g u
  let h' : (F.spanApex f g u).subgroup →* F.imageSubgroup g :=
    { toFun := fun x => ⟨(h.val x).val, by
        obtain ⟨y, hy⟩ := F.spanConjugate_mem_range f g u x
        exact ⟨y, congrArg Subtype.val hy⟩⟩
      map_one' := by
        apply Subtype.ext
        change (h.val 1).val = (1 : S)
        exact congrArg (fun z : T.subgroup => z.val) (map_one h.val)
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (h.val (x * y)).val = (h.val x).val * (h.val y).val
        exact congrArg (fun z : T.subgroup => z.val) (map_mul h.val x y) }
  refine ⟨h', F.codomain_restrict_mem h.val h.property (F.image_le g) h' ?_⟩
  ext x
  rfl

def concreteSpan {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup) :
    MackeySpan F.Object P Q where
  apex := F.spanApex f g u
  left := F.spanLeft f g u
  right := F.spanToImage f g u ≫ (F.imageIso g).inv

def orbitRepresentative {P Q : F.Orbit} (f : P ⟶ Q) : P.as ⟶ Q.as :=
  F.toOrbit.preimage f

theorem orbitRepresentative_map {P Q : F.Orbit} (f : P ⟶ Q) :
    F.toOrbit.map (F.orbitRepresentative f) = f := F.toOrbit.map_preimage f

def DoubleCosetTerm {P Q T : F.Orbit} (f : P ⟶ T) (g : Q ⟶ T) : Type u :=
  DoubleCoset.Quotient ((F.orbitRepresentative f).val.range : Set T.as.subgroup)
    ((F.orbitRepresentative g).val.range : Set T.as.subgroup)

instance doubleCosetTermFinite [Finite S] {P Q T : F.Orbit} (f : P ⟶ T) (g : Q ⟶ T) :
    Fintype (F.DoubleCosetTerm f g) := by
  unfold DoubleCosetTerm DoubleCoset.Quotient
  exact Fintype.ofFinite _

def doubleCosetSpan {P Q T : F.Orbit} (f : P ⟶ T) (g : Q ⟶ T)
    (i : F.DoubleCosetTerm f g) : MackeySpan F.Orbit P Q :=
  let t := F.concreteSpan (F.orbitRepresentative f) (F.orbitRepresentative g) i.out
  { apex := F.toOrbit.obj t.apex
    left := F.toOrbit.map t.left
    right := F.toOrbit.map t.right }

def mackeyShape [Finite S] : MackeyShape F.Orbit where
  rank := F.orbitOrder
  rank_mono := F.orbitOrder_mono
  iso_of_rank := F.orbit_isIso_of_equal_order
  Term := F.DoubleCosetTerm
  termFintype := F.doubleCosetTermFinite
  span := F.doubleCosetSpan

abbrev FullMackey (R : Type w) [Ring R] [Finite S] :=
  MackeyModule R F.Orbit F.mackeyShape

/-- Generation for full Mackey coefficients on the actual fusion orbit
category. The classification/minimality hypotheses are precisely the
published simple-functor input, not the conclusion being proved. -/
theorem simple_transfer_generation [Finite S] {k : Type w} [Field k]
    (M : F.FullMackey k) (Q : F.Orbit)
    (small_zero : ∀ P, F.orbitOrder P < F.orbitOrder Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple) (nonzero : ∃ x : M.Value Q, x ≠ 0) :
    ∀ P, M.generated Q P = ⊤ :=
  M.transfer_generation Q small_zero simple nonzero

theorem simple_restriction_detection [Finite S] {k : Type w} [Field k]
    (M : F.FullMackey k) (Q : F.Orbit)
    (small_zero : ∀ P, F.orbitOrder P < F.orbitOrder Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple) (nonzero : ∃ x : M.Value Q, x ≠ 0) (P : F.Orbit) :
    Function.Injective (restrictionProduct
      (fun s : MackeyModule.SeedMap Q P => M.pull s.2.2)) :=
  M.restriction_detection Q small_zero simple nonzero P

end Sharpness.FusionSystem
