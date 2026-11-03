import Sharpness.Unconditional.BurnsideMarks
import Sharpness.FusionMackey
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
Nondegeneracy of finite tables of categorical marks, including slice
categories. The ranks and equal-rank isomorphisms are supplied by actual
subgroup orders when this is applied to fusion orbit categories.
-/

set_option autoImplicit false
noncomputable section
universe u v w t

namespace Sharpness.Burnside

open CategoryTheory

variable {C : Type v} [Category.{w} C]
    {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
    {ι : Type t} [Fintype ι] [DecidableEq ι]

/-- The categorical table of marks on a collection of objects. -/
def homCountMatrix (R : Type u) [CommRing R] (X : ι → C) : Matrix ι ι R :=
  fun i j => (Nat.card (X i ⟶ X j) : R)

/-- A finite collection of pairwise nonisomorphic objects in a ranked EI
category has a nondegenerate table of marks in characteristic zero. -/
theorem homCountMatrix_det_ne_zero [∀ P Q : C, Finite (P ⟶ Q)]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    (X : ι → C) (separated : ∀ i j, (X i ≅ X j) → i = j) :
    (homCountMatrix R X).det ≠ 0 := by
  apply det_ne_zero_of_rank (homCountMatrix R X) (fun i => rank (X i))
  · intro i j hij
    letI : IsEmpty (X i ⟶ X j) := ⟨fun f => (not_le_of_gt hij (rank_mono f)).elim⟩
    simp [homCountMatrix]
  · intro i j hij hne
    letI : IsEmpty (X i ⟶ X j) := ⟨fun f => by
      letI := iso_of_rank f hij
      exact hne (separated i j (asIso f))⟩
    simp [homCountMatrix]
  · intro i
    letI : Nonempty (X i ⟶ X i) := ⟨𝟙 (X i)⟩
    change (Nat.card (X i ⟶ X i) : R) ≠ 0
    exact_mod_cast (Nat.ne_of_gt (Nat.card_pos (α := X i ⟶ X i)))

/-- The hom-count marks of a virtual finite sum, with its coefficients in R. -/
def additiveMarkMap (R : Type u) [CommRing R] (X : ι → C) :
    (ι → R) →ₗ[R] (ι → R) := (homCountMatrix R X).mulVecLin

/-- Marks distinguish virtual sums of pairwise nonisomorphic objects. -/
theorem additiveMarkMap_injective [∀ P Q : C, Finite (P ⟶ Q)]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    (X : ι → C) (separated : ∀ i j, (X i ≅ X j) → i = j) :
    Function.Injective (additiveMarkMap R X) :=
  Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (homCountMatrix_det_ne_zero rank rank_mono iso_of_rank X separated))

/-- Finite categories have finite skeletons. -/
instance skeletonFinite [Finite C] : Finite (Skeleton C) := by
  exact Finite.of_surjective (toSkeleton : C → Skeleton C) fun X =>
    ⟨(fromSkeleton C).obj X, toSkeleton_fromSkeleton_obj X⟩

/-- Finite categories with finite hom sets have finite slice categories. -/
instance overFinite [Finite C] [∀ P Q : C, Finite (P ⟶ Q)] (P : C) :
    Finite (Over P) := by
  apply Finite.of_surjective (fun a : Σ Q : C, Q ⟶ P => Over.mk a.2)
  intro a
  exact ⟨⟨a.left, a.hom⟩, rfl⟩

instance overHomFinite [∀ P Q : C, Finite (P ⟶ Q)] (P : C) (X Y : Over P) :
    Finite (X ⟶ Y) := by
  apply Finite.of_injective (fun f : X ⟶ Y => f.left)
  exact fun _ _ h => Over.OverMorphism.ext h

local instance fullSubcategoryFinite [Finite C] (K : ObjectProperty C) :
    Finite K.FullSubcategory :=
  Finite.of_injective (fun X : K.FullSubcategory => X.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance fullSubcategoryHomFinite [∀ P Q : C, Finite (P ⟶ Q)]
    (K : ObjectProperty C) (X Y : K.FullSubcategory) : Finite (X ⟶ Y) :=
  Finite.of_injective (fun f : X ⟶ Y => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

/-- Equal-rank arrows are also isomorphisms in every full subcategory. -/
theorem fullSubcategory_iso_of_rank (K : ObjectProperty C)
    (rank : C → ℕ)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    {X Y : K.FullSubcategory} (f : X ⟶ Y)
    (h : rank X.obj = rank Y.obj) : IsIso f := by
  letI : IsIso f.hom := iso_of_rank f.hom h
  letI : IsIso (K.ι.map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f K.ι

/-- The table of marks indexed by all isomorphism classes is nondegenerate. -/
theorem skeleton_homCountMatrix_det_ne_zero [Finite C]
    [∀ P Q : C, Finite (P ⟶ Q)]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f) :
    letI := Fintype.ofFinite (Skeleton C)
    letI := Classical.decEq (Skeleton C)
    (homCountMatrix R (fromSkeleton C).obj).det ≠ 0 := by
  classical
  letI := Fintype.ofFinite (Skeleton C)
  apply homCountMatrix_det_ne_zero rank rank_mono iso_of_rank
  intro i j e
  exact skeleton_skeletal C ⟨(fromSkeleton C).preimageIso e⟩

/-- The rank conditions pass to the actual slice category. -/
theorem over_iso_of_rank
    (rank : C → ℕ)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    {P : C} {X Y : Over P} (f : X ⟶ Y)
    (h : rank X.left = rank Y.left) : IsIso f := by
  letI : IsIso f.left := iso_of_rank f.left h
  letI : IsIso ((Over.forget P).map f) := by
    change IsIso f.left
    infer_instance
  exact isIso_of_reflects_iso f (Over.forget P)

/-- In particular, the mark matrix needed for each slice Burnside algebra is
nondegenerate. This does not require saturation. -/
theorem over_skeleton_homCountMatrix_det_ne_zero [Finite C]
    [∀ P Q : C, Finite (P ⟶ Q)]
    (rank : C → ℕ)
    (rank_mono : ∀ {P Q : C}, (P ⟶ Q) → rank P ≤ rank Q)
    (iso_of_rank : ∀ {P Q : C} (f : P ⟶ Q), rank P = rank Q → IsIso f)
    (P : C) :
    letI := Fintype.ofFinite (Skeleton (Over P))
    letI := Classical.decEq (Skeleton (Over P))
    (homCountMatrix R (fromSkeleton (Over P)).obj).det ≠ 0 := by
  classical
  letI := Fintype.ofFinite (Skeleton (Over P))
  exact skeleton_homCountMatrix_det_ne_zero (R := R)
    (fun X : Over P => rank X.left)
    (fun f => rank_mono f.left)
    (fun f h => over_iso_of_rank rank iso_of_rank f h)

/-- The actual centric fusion orbit category has nondegenerate slice tables
of marks. Saturation is needed later for the prime-to-p mark values, but is
not needed for this determinant theorem. -/
theorem centric_slice_markMatrix_det_ne_zero
    {S : Type v} [Group S] [Finite S] (F : FusionSystem S)
    (P : F.CentricOrbit) :
    letI := Fintype.ofFinite (Skeleton (Over P))
    letI := Classical.decEq (Skeleton (Over P))
    (homCountMatrix R (fromSkeleton (Over P)).obj).det ≠ 0 := by
  classical
  letI := Fintype.ofFinite (Skeleton (Over P))
  exact over_skeleton_homCountMatrix_det_ne_zero (R := R)
    (fun X : F.CentricOrbit => F.orbitOrder X.obj)
    (fun {X Y : F.CentricOrbit} (f : X ⟶ Y) => F.orbitOrder_mono f.hom)
    (fun {X Y : F.CentricOrbit} (f : X ⟶ Y) h => fullSubcategory_iso_of_rank _ F.orbitOrder
      F.orbit_isIso_of_equal_order f h) P

/-- The integral or p-local additive marks distinguish virtual objects in
the actual centric slice. -/
theorem centric_slice_additiveMarkMap_injective
    {S : Type v} [Group S] [Finite S] (F : FusionSystem S)
    (P : F.CentricOrbit) :
    letI := Fintype.ofFinite (Skeleton (Over P))
    Function.Injective (additiveMarkMap R (fromSkeleton (Over P)).obj) := by
  classical
  letI := Fintype.ofFinite (Skeleton (Over P))
  exact Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (centric_slice_markMatrix_det_ne_zero (R := R) F P))

end Sharpness.Burnside
