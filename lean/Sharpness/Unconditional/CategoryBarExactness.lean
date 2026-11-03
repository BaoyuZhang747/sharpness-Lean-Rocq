import Sharpness.Unconditional.CategoryBarConstruction
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-! Pointwise contraction of the augmented category bar construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Insert the evaluation object as the first vertex of a string. -/
def categoryBarInsert (n : ℕ) (X : Cᵒᵖ) :
    (categoryBarTerm R C n).obj X ⟶ (categoryBarTerm R C (n + 1)).obj X :=
  (ModuleCat.free R).map
    (↾fun b => ⟨b.1.precomp b.2, 𝟙 X.unop⟩ :
      categoryBarBasis C n X ⟶ categoryBarBasis C (n + 1) X)

/-- The augmentation is surjective at every object: a constant string at
that object provides a generator mapping to `1`. -/
instance categoryBarAugmentation_epi (n : ℕ) :
    Epi (categoryBarAugmentation (R := R) (C := C) n) := by
  apply (NatTrans.epi_iff_epi_app' (ModuleCat.{u} R) _).mpr
  intro X
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro r
  change R at r
  let s : ComposableArrows C n := (CategoryTheory.Functor.const _).obj X.unop
  refine ⟨r • ModuleCat.freeMk (⟨s, 𝟙 _⟩ : categoryBarBasis C n X), ?_⟩
  rw [map_smul, categoryBarAugmentation_freeMk]
  exact mul_one r

theorem categoryChain_restrict_zero_precomp {n : ℕ} (s : ComposableArrows C n)
    {X : C} (g : X ⟶ chainHead s) :
    restrictCategoryChain (SimplexCategory.δ 0) (s.precomp g) = s := by
  refine CategoryTheory.Functor.ext (fun a => rfl) ?_
  intro a b f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

@[simp]
theorem categoryChain_restrict_face_obj {n : ℕ} (s : ComposableArrows C (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (restrictCategoryChain (SimplexCategory.δ i) s).obj j = s.obj (i.succAbove j) := rfl

@[simp]
theorem categoryChain_restrict_face_map {n : ℕ} (s : ComposableArrows C (n + 1))
    (i : Fin (n + 2)) {a b : Fin (n + 1)} (f : a ⟶ b) :
    (restrictCategoryChain (SimplexCategory.δ i) s).map f =
      s.map (homOfLE ((Fin.succAboveOrderEmb i).monotone (leOfHom f))) := rfl

@[simp]
theorem categoryChain_precomp_map_succ {n : ℕ} (s : ComposableArrows C n)
    {X : C} (g : X ⟶ chainHead s) {a b : Fin (n + 1)} (h : a.succ ≤ b.succ) :
    (s.precomp g).map (homOfLE h) = s.map (homOfLE (Fin.succ_le_succ_iff.mp h)) := rfl

@[simp]
theorem categoryChain_precomp_map_zero_succ {n : ℕ} (s : ComposableArrows C n)
    {X : C} (g : X ⟶ chainHead s) (b : Fin (n + 1)) :
    (s.precomp g).map (homOfLE (show (0 : Fin (n + 2)) ≤ b.succ from Fin.zero_le _)) =
      g ≫ s.map (homOfLE (Fin.zero_le b)) := by
  rcases b with ⟨_ | b, hb⟩
  · change g = g ≫ s.map (𝟙 _)
    simp
  · rfl

theorem categoryChain_precomp_map_zero_one_heq {n : ℕ} (s : ComposableArrows C n)
    {X : C} (g : X ⟶ chainHead s) {a b : Fin (n + 2)} (h : a ≤ b)
    (ha : a = 0) (hb : b = 1) :
    HEq (ComposableArrows.Precomp.map s g a b h) g := by
  subst a
  subst b
  rfl

theorem categoryChain_precomp_map_zero_zero_heq {n : ℕ} (s : ComposableArrows C n)
    {X : C} (g : X ⟶ chainHead s) {a b : Fin (n + 2)} (h : a ≤ b)
    (ha : a = 0) (hb : b = 0) :
    HEq (ComposableArrows.Precomp.map s g a b h) (𝟙 X) := by
  subst a
  subst b
  rfl

theorem categoryChain_restrict_succ_precomp {n : ℕ} (s : ComposableArrows C (n + 1))
    {X : C} (g : X ⟶ chainHead s) (i : Fin (n + 2)) :
    restrictCategoryChain (SimplexCategory.δ i.succ) (s.precomp g) =
      (restrictCategoryChain (SimplexCategory.δ i) s).precomp
        (g ≫ categoryChainHeadArrow (SimplexCategory.δ i) s) := by
  have htail : (restrictCategoryChain (SimplexCategory.δ i.succ) (s.precomp g)).δ₀ =
      restrictCategoryChain (SimplexCategory.δ i) s := by
    change restrictCategoryChain (SimplexCategory.δ 0)
      (restrictCategoryChain (SimplexCategory.δ i.succ) (s.precomp g)) = _
    rw [← restrictCategoryChain_comp, SimplexCategory.δ_comp_δ (Fin.zero_le i),
      restrictCategoryChain_comp]
    exact congrArg (restrictCategoryChain (SimplexCategory.δ i))
      (categoryChain_restrict_zero_precomp s g)
  refine ComposableArrows.ext_succ ?_ (by simpa using htail) ?_
  · change (s.precomp g).obj (i.succ.succAbove 0) = X
    rw [Fin.succ_succAbove_zero]
    rfl
  · cases i using Fin.cases
    all_goals simp only [ComposableArrows.precomp_map,
      categoryChain_restrict_face_map]
    all_goals dsimp only [ComposableArrows.Precomp.map]
    all_goals try simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    all_goals try rfl
    rename_i j
    simp only [Fin.succAboveOrderEmb_apply]
    dsimp only [categoryChainHeadArrow]
    simp [SimplexCategory.δ, SimplexCategory.toCat]
    exact eq_of_heq (categoryChain_precomp_map_zero_one_heq s g
      (a := j.succ.succ.succAbove 0) (b := j.succ.succ.succAbove 1)
      ((Fin.succAboveOrderEmb j.succ.succ).monotone (Fin.zero_le _))
      (by simp)
      (by simp [Fin.succ_succAbove_one]))

/-- The first face cancels insertion of the initial evaluation object. -/
theorem categoryBarInsert_comp_face_zero (n : ℕ) (X : Cᵒᵖ) :
    categoryBarInsert (R := R) n X ≫ (categoryBarMap (SimplexCategory.δ 0)).app X =
      𝟙 ((categoryBarTerm R C n).obj X) := by
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (categoryBarMap (R := R) (SimplexCategory.δ 0)).app X
      ((categoryBarInsert (R := R) n X) (ModuleCat.freeMk (R := R) ⟨s, g⟩)) =
    ModuleCat.freeMk (R := R) ⟨s, g⟩
  simp only [categoryBarInsert, categoryBarMap, ModuleCat.free_map_apply]
  apply congrArg (ModuleCat.freeMk (R := R))
  apply Sigma.ext (categoryChain_restrict_zero_precomp s g)
  change HEq ((𝟙 X.unop) ≫ categoryChainHeadArrow (SimplexCategory.δ 0) (s.precomp g)) g
  simp only [Category.id_comp]
  rfl

/-- Every other face commutes with insertion, shifted by one place. -/
theorem categoryBarInsert_comp_face_succ (n : ℕ) (X : Cᵒᵖ) (i : Fin (n + 2)) :
    categoryBarInsert (R := R) (n + 1) X ≫ (categoryBarMap (SimplexCategory.δ i.succ)).app X =
      (categoryBarMap (SimplexCategory.δ i)).app X ≫ categoryBarInsert n X := by
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (categoryBarMap (SimplexCategory.δ i.succ)).app X
      ((categoryBarInsert (R := R) (n + 1) X) (ModuleCat.freeMk ⟨s, g⟩)) =
    categoryBarInsert n X ((categoryBarMap (SimplexCategory.δ i)).app X (ModuleCat.freeMk ⟨s, g⟩))
  simp only [categoryBarInsert, categoryBarMap, ModuleCat.free_map_apply]
  apply congrArg (ModuleCat.freeMk (R := R))
  apply Sigma.ext (categoryChain_restrict_succ_precomp s g i)
  simp [categoryChainHeadArrow, SimplexCategory.δ, SimplexCategory.toCat]
  apply eq_of_heq
  apply categoryChain_precomp_map_zero_zero_heq s g _ rfl
  change i.succ.succAbove 0 = 0
  simp

end Sharpness.Unconditional
