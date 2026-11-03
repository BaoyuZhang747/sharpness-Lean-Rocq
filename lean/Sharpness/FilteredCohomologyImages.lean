import Sharpness.LinearImageQuotient
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Images in degree n of an actual decreasing functor of cochain
complexes, with target its zeroth filtration term. The image quotient is
identified with the corresponding filtration quotient, with all maps
fixed by the actual functor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (I : ℕᵒᵈ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

def filteredCohomologyMap (a b : ℕ) (h : b ≤ a) :
    (I.obj (OrderDual.toDual a)).homology n ⟶ (I.obj (OrderDual.toDual b)).homology n :=
  HomologicalComplex.homologyMap
    (I.map (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from h))) n

theorem filteredCohomologyMap_comp (a b c : ℕ) (hb : b ≤ a) (hc : c ≤ b) :
    filteredCohomologyMap I n a b hb ≫ filteredCohomologyMap I n b c hc =
      filteredCohomologyMap I n a c (hc.trans hb) := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (I.map_comp _ _).symm)

def filteredCohomologyImage (k : ℕ) : Submodule R ((I.obj (OrderDual.toDual 0)).homology n) :=
  LinearMap.range (filteredCohomologyMap I n k 0 (Nat.zero_le k)).hom

theorem filteredCohomologyImage_antitone : Antitone (filteredCohomologyImage I n) := by
  intro k l h
  rintro x ⟨y, rfl⟩
  refine ⟨filteredCohomologyMap I n l k h y, ?_⟩
  exact congrArg (fun f => f y) (filteredCohomologyMap_comp I n l k 0 h (Nat.zero_le k))

theorem filteredCohomologyImage_start : filteredCohomologyImage I n 0 = ⊤ := by
  have he : filteredCohomologyMap I n 0 0 le_rfl = 𝟙 _ := by
    dsimp only [filteredCohomologyMap]
    change HomologicalComplex.homologyMap (I.map (𝟙 (OrderDual.toDual 0))) n = _
    rw [I.map_id, HomologicalComplex.homologyMap_id]
  exact (congrArg (fun f => LinearMap.range f.hom) he).trans LinearMap.range_id

theorem filteredCohomologyImage_zero (k : ℕ)
    (h : IsZero ((I.obj (OrderDual.toDual k)).homology n)) : filteredCohomologyImage I n k = ⊥ := by
  have he : filteredCohomologyMap I n k 0 (Nat.zero_le k) = 0 := h.eq_of_src _ _
  exact (congrArg (fun f : (I.obj (OrderDual.toDual k)).homology n ⟶
    (I.obj (OrderDual.toDual 0)).homology n => LinearMap.range f.hom) he).trans LinearMap.range_zero

def filteredCohomologyImageQuotientIso (p : ℕ) :
    ModuleCat.of R (ImageQuotient (filteredCohomologyMap I n (p+1) p (Nat.le_succ p)).hom
      (filteredCohomologyMap I n p 0 (Nat.zero_le p)).hom) ≅
    ModuleCat.of R (filteredCohomologyImage I n p ⧸
      (filteredCohomologyImage I n (p+1)).comap (filteredCohomologyImage I n p).subtype) := by
  have he := congrArg (fun f => f.hom)
    (filteredCohomologyMap_comp I n (p+1) p 0 (Nat.le_succ p) (Nat.zero_le p))
  exact (Submodule.quotEquivOfEq _ _ (congrArg
    (fun f => (LinearMap.range f).comap (filteredCohomologyImage I n p).subtype) he)).toModuleIso

end Sharpness
