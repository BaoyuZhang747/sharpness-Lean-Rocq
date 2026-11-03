import Sharpness.ArbitraryCoefficients
import Sharpness.Unconditional.BarCalculation
import Sharpness.Unconditional.DegreeZero

/-!
Lemma 2.2(ii) of the revised manuscript, in one fixed degree over an arbitrary
commutative ring. A finite set of coordinates lies in a full Mackey subfunctor
with finitely generated values. In positive degree we lift a bar cocycle; in
degree zero we lift its compatible family. No saturation is required.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)

local instance : Finite F.CentricOrbit :=
  Finite.of_injective (fun P => P.obj) (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance (P Q : F.CentricOrbit) : Finite (P ⟶ Q) :=
  Finite.of_injective (fun f : P ⟶ Q => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

/-- The degree-zero case of finite-generation closure, using actual compatible
families rather than a positive-degree vanishing hypothesis. -/
theorem higherLimit_zero_isZero_of_fg_subfunctors
    (h : ∀ N : M.Subfunctor, (∀ P, (N.obj P).FG) →
      IsZero (higherLimit (F.centricCoefficient (M.submodule N)) 0)) :
    IsZero (higherLimit (F.centricCoefficient M) 0) := by
  classical
  let D := (F.coefficientData M).onFull F.centricProperty
  apply IsZero.of_iso (Y := ModuleCat.of R D.limit) _ D.higherLimitZeroIso
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro z
  letI : Fintype F.CentricOrbit := Fintype.ofFinite _
  let label : F.CentricOrbit → Σ P : F.Orbit, M.Value P :=
    fun P => ⟨P.obj, z.val P⟩
  let X : Finset (Σ P : F.Orbit, M.Value P) := Finset.univ.image label
  let N := M.finiteGeneratedSubfunctor X
  have memN (P : F.CentricOrbit) : z.val P ∈ N.obj P.obj := by
    apply Submodule.subset_span
    refine ⟨label P, Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩,
      ⟨P.obj, 𝟙 _, 𝟙 _⟩, ?_⟩
    simp [MackeyModule.normalMap, M.pull_id, M.push_id, label]
  let DN := (F.coefficientData (M.submodule N)).onFull F.centricProperty
  let zN : DN.limit := ⟨fun P => ⟨z.val P, memN P⟩, by
    intro P Q f
    apply Subtype.ext
    exact z.property f⟩
  haveI : Subsingleton DN.limit := ModuleCat.isZero_iff_subsingleton.mp
    (IsZero.of_iso (h N (fun P => M.finiteGeneratedValue_fg X P))
      DN.higherLimitZeroIso.symm)
  have hzN : zN = 0 := Subsingleton.elim _ _
  apply Subtype.ext
  funext P
  exact congrArg (fun x : DN.limit => (x.val P).val) hzN

/-- In a fixed positive degree, all coordinates of a cocycle lie in one
finitely generated full Mackey subfunctor. Only that degree is used. -/
theorem higherLimit_succ_isZero_of_fg_subfunctors (n : ℕ)
    (h : ∀ N : M.Subfunctor, (∀ P, (N.obj P).FG) →
      IsZero (higherLimit (F.centricCoefficient (M.submodule N)) (n + 1))) :
    IsZero (higherLimit (F.centricCoefficient M) (n + 1)) := by
  classical
  let B := Unconditional.finiteCategoryBarModel R F.CentricOrbit
  let cmp := Unconditional.finiteCategoryBarComparison R F.CentricOrbit
  apply IsZero.of_iso (Y := ModuleCat.of R (B.Cohomology (F.centricCoefficient M) n))
    _ (cmp.AKO_III_5_3 _ n)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  refine Quotient.inductionOn' x fun z => ?_
  let label : B.Index (n + 1) → Σ P : F.Orbit, M.Value P :=
    fun i => ⟨(B.source (n + 1) i).unop.obj, z.val i⟩
  let X : Finset (Σ P : F.Orbit, M.Value P) := Finset.univ.image label
  let N := M.finiteGeneratedSubfunctor X
  have memN (i : B.Index (n + 1)) :
      z.val i ∈ N.obj (B.source (n + 1) i).unop.obj := by
    apply Submodule.subset_span
    refine ⟨label i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      ⟨(B.source (n + 1) i).unop.obj, 𝟙 _, 𝟙 _⟩, ?_⟩
    simp [MackeyModule.normalMap, M.pull_id, M.push_id, label]
  let zN : B.Cochains (F.centricCoefficient (M.submodule N)) (n + 1) :=
    fun i => ⟨z.val i, memN i⟩
  let inc := F.subCoefficientInclusion M N
  have lifted : B.map inc (n + 1) zN = z.val := rfl
  have closed : B.d (F.centricCoefficient (M.submodule N)) (n + 1) zN = 0 := by
    apply B.map_injective inc (fun _ => Subtype.val_injective) (n + 2)
    rw [map_zero, B.map_d, lifted]
    exact z.property
  haveI : Subsingleton (B.Cohomology (F.centricCoefficient (M.submodule N)) n) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (IsZero.of_iso (h N (fun P => M.finiteGeneratedValue_fg X P))
        (cmp.AKO_III_5_3 _ n).symm)
  have hzN : (LinearMap.range (B.boundary (F.centricCoefficient (M.submodule N)) n)).mkQ
      ⟨zN, closed⟩ = 0 := Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzN
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨B.map inc n b, ?_⟩
  apply Subtype.ext
  change B.d (F.centricCoefficient M) n (B.map inc n b) = z.val
  rw [← B.map_d, show B.d (F.centricCoefficient (M.submodule N)) n b = zN
    from congrArg Subtype.val hb, lifted]

/-- Manuscript Lemma 2.2(ii): finite-generation closure in one fixed degree,
including degree zero, over every commutative ring and without saturation. -/
theorem higherLimit_isZero_of_fg_subfunctors (n : ℕ)
    (h : ∀ N : M.Subfunctor, (∀ P, (N.obj P).FG) →
      IsZero (higherLimit (F.centricCoefficient (M.submodule N)) n)) :
    IsZero (higherLimit (F.centricCoefficient M) n) := by
  cases n with
  | zero => exact F.higherLimit_zero_isZero_of_fg_subfunctors M h
  | succ n => exact F.higherLimit_succ_isZero_of_fg_subfunctors M n h

end Sharpness.FusionSystem
