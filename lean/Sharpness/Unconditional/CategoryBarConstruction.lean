import Sharpness.CoefficientCochainFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
The free-representable bar construction for an arbitrary small category.
Its degree `n` basis at `X` consists of a string `s` and an arrow from `X`
to the first object of `s`. The linear Yoneda correspondence identifies maps
out of this diagram with the explicit coefficient cochains already used in
the project. No bar-comparison theorem is assumed in this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable (R C : Type u) [CommRing R] [Category.{u} C]

/-- The representable generators of the unnormalized bar term. -/
abbrev categoryBarBasis (n : ℕ) (X : Cᵒᵖ) :=
  Σ s : ComposableArrows C n, X.unop ⟶ chainHead s

/-- The free module on all strings starting after the evaluation object. -/
abbrev categoryBarTerm (n : ℕ) : CoefficientCategory R C where
  obj X := (ModuleCat.free R).obj (categoryBarBasis C n X)
  map {X Y} f := (ModuleCat.free R).map
    (↾fun b => ⟨b.1, f.unop ≫ b.2⟩ : categoryBarBasis C n X ⟶ categoryBarBasis C n Y)
  map_id X := by
    apply ModuleCat.free_hom_ext
    intro b
    simp
  map_comp f g := by
    apply ModuleCat.free_hom_ext
    intro b
    simp [Category.assoc]

variable {R C}

@[simp]
theorem categoryBarTerm_map_freeMk {n : ℕ} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : ComposableArrows C n) (g : X.unop ⟶ chainHead s) :
    (categoryBarTerm R C n).map f (ModuleCat.freeMk ⟨s, g⟩) =
      ModuleCat.freeMk ⟨s, f.unop ≫ g⟩ :=
  ModuleCat.free_map_apply _ _

/-- A map from a bar term is specified by one element for each string. -/
def categoryBarDesc {n : ℕ} (M : CoefficientCategory R C)
    (x : ∀ s : ComposableArrows C n, M.obj (op (chainHead s))) :
    categoryBarTerm R C n ⟶ M where
  app X := ModuleCat.freeDesc (↾fun b => M.map b.2.op (x b.1))
  naturality {X Y} f := by
    apply ModuleCat.free_hom_ext
    rintro ⟨s, g⟩
    change (ModuleCat.freeDesc (↾fun b : categoryBarBasis C n Y => M.map b.2.op (x b.1)))
        ((categoryBarTerm R C n).map f (ModuleCat.freeMk ⟨s, g⟩)) =
      M.map f ((ModuleCat.freeDesc (↾fun b : categoryBarBasis C n X => M.map b.2.op (x b.1)))
        (ModuleCat.freeMk ⟨s, g⟩))
    simp [op_comp, Functor.map_comp]

@[simp]
theorem categoryBarDesc_freeMk {n : ℕ} (M : CoefficientCategory R C)
    (x : ∀ s : ComposableArrows C n, M.obj (op (chainHead s)))
    (X : Cᵒᵖ) (s : ComposableArrows C n) (g : X.unop ⟶ chainHead s) :
    (categoryBarDesc M x).app X (ModuleCat.freeMk ⟨s, g⟩) = M.map g.op (x s) :=
  ModuleCat.freeDesc_apply _ _

/-- The linear Yoneda correspondence for the bar term, including infinite
sets of strings (the domain is a coproduct and the codomain a product). -/
def categoryBarHomEquiv (n : ℕ) (M : CoefficientCategory R C) :
    (categoryBarTerm R C n ⟶ M) ≃ₗ[R]
      (∀ s : ComposableArrows C n, M.obj (op (chainHead s))) where
  toFun α s := α.app (op (chainHead s)) (ModuleCat.freeMk ⟨s, 𝟙 _⟩)
  invFun := categoryBarDesc M
  left_inv α := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.free_hom_ext
    intro b
    rcases b with ⟨s, g⟩
    have h := congrArg (fun t => t (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) (α.naturality g.op)
    change α.app X ((categoryBarTerm R C n).map g.op (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) =
      M.map g.op (α.app _ (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) at h
    erw [categoryBarDesc_freeMk]
    simpa using h.symm
  right_inv x := by
    funext s
    simp [categoryBarDesc]
  map_add' α β := rfl
  map_smul' a α := rfl

@[simp]
theorem categoryBarHomEquiv_comp {n : ℕ} {M N : CoefficientCategory R C}
    (α : categoryBarTerm R C n ⟶ M) (f : M ⟶ N) (s : ComposableArrows C n) :
    categoryBarHomEquiv n N (α ≫ f) s =
      f.app (op (chainHead s)) (categoryBarHomEquiv n M α s) := rfl

/-- Each bar term is projective, by lifting its string generators
independently through a pointwise epimorphism. -/
instance categoryBarTerm_projective (n : ℕ) : Projective (categoryBarTerm R C n) where
  factors {E M} f e he := by
    have hs (s : ComposableArrows C n) :
        ∃ x : E.obj (op (chainHead s)),
          e.app _ x = categoryBarHomEquiv n M f s :=
      (ModuleCat.epi_iff_surjective (e.app _)).mp
        ((NatTrans.epi_iff_epi_app' (ModuleCat.{u} R) e).mp he _) _
    choose x hx using hs
    refine ⟨(categoryBarHomEquiv n E).symm x, ?_⟩
    apply (categoryBarHomEquiv n M).injective
    funext s
    simpa using hx s

/-- The simplicial map sends a generator to the restricted string and
composes its incoming arrow with the induced head arrow. -/
def categoryBarMap {i j : SimplexCategory} (f : i ⟶ j) :
    categoryBarTerm R C j.len ⟶ categoryBarTerm R C i.len where
  app X := (ModuleCat.free R).map
    (↾fun b => ⟨restrictCategoryChain f b.1, b.2 ≫ categoryChainHeadArrow f b.1⟩ :
      categoryBarBasis C j.len X ⟶ categoryBarBasis C i.len X)
  naturality {X Y} g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨s, h⟩
    change (ModuleCat.free R).map
      (↾fun b : categoryBarBasis C j.len Y =>
        (⟨restrictCategoryChain f b.1, b.2 ≫ categoryChainHeadArrow f b.1⟩ : categoryBarBasis C i.len Y))
      ((categoryBarTerm R C j.len).map g
        (ModuleCat.freeMk ⟨s, h⟩)) =
      (categoryBarTerm R C i.len).map g ((ModuleCat.free R).map
        (↾fun b : categoryBarBasis C j.len X =>
          (⟨restrictCategoryChain f b.1, b.2 ≫ categoryChainHeadArrow f b.1⟩ : categoryBarBasis C i.len X))
        (ModuleCat.freeMk ⟨s, h⟩))
    simp [Category.assoc]

@[simp]
theorem categoryBarMap_freeMk {i j : SimplexCategory} (f : i ⟶ j)
    (X : Cᵒᵖ) (s : ComposableArrows C j.len) (g : X.unop ⟶ chainHead s) :
    (categoryBarMap (R := R) f).app X (ModuleCat.freeMk ⟨s, g⟩) =
      ModuleCat.freeMk ⟨restrictCategoryChain f s, g ≫ categoryChainHeadArrow f s⟩ :=
  ModuleCat.free_map_apply _ _

@[simp]
theorem categoryBarMap_id (i : SimplexCategory) :
    categoryBarMap (R := R) (C := C) (𝟙 i) = 𝟙 (categoryBarTerm R C i.len) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (categoryBarMap (R := R) (𝟙 i)).app X (ModuleCat.freeMk ⟨s, g⟩) =
    ModuleCat.freeMk ⟨s, g⟩
  simp [categoryBarMap, restrictCategoryChain_id, categoryChainHeadArrow_id]

@[simp]
theorem categoryBarMap_comp {i j k : SimplexCategory} (f : i ⟶ j) (g : j ⟶ k) :
    categoryBarMap (R := R) (C := C) (f ≫ g) = categoryBarMap g ≫ categoryBarMap f := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, h⟩
  change (categoryBarMap (R := R) (f ≫ g)).app X (ModuleCat.freeMk ⟨s, h⟩) =
    (categoryBarMap f).app X ((categoryBarMap g).app X (ModuleCat.freeMk ⟨s, h⟩))
  simp [categoryBarMap, restrictCategoryChain_comp, categoryChainHeadArrow_comp, Category.assoc]

/-- The bar simplicial map induces precisely the already-defined coefficient
replacement map, including its first face involving coefficient transport. -/
theorem categoryBarHomEquiv_map {i j : SimplexCategory} (f : i ⟶ j)
    (M : CoefficientCategory R C) (α : categoryBarTerm R C i.len ⟶ M) :
    categoryBarHomEquiv j.len M (categoryBarMap f ≫ α) =
      coefficientReplacementMap M f (categoryBarHomEquiv i.len M α) := by
  funext s
  change α.app (op (chainHead s))
      ((categoryBarMap f).app _ (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) =
    M.map (categoryChainHeadArrow f s).op
      (α.app (op (chainHead (restrictCategoryChain f s)))
        (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩))
  have h := congrArg
    (fun t => t (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩))
    (α.naturality (categoryChainHeadArrow f s).op)
  change α.app (op (chainHead s))
      ((categoryBarTerm R C i.len).map (categoryChainHeadArrow f s).op
        (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩)) = _ at h
  simpa [categoryBarMap] using h

/-- Every bar generator augments to `1` in the constant diagram. -/
def categoryBarAugmentation (n : ℕ) : categoryBarTerm R C n ⟶ constantCoefficient R C :=
  categoryBarDesc (constantCoefficient R C) (fun _ => (1 : R))

@[simp]
theorem categoryBarAugmentation_freeMk (n : ℕ) (X : Cᵒᵖ)
    (s : ComposableArrows C n) (g : X.unop ⟶ chainHead s) :
    (categoryBarAugmentation (R := R) n).app X (ModuleCat.freeMk ⟨s, g⟩) = (1 : R) :=
  categoryBarDesc_freeMk _ _ _ _ _

@[simp]
theorem categoryBarMap_augmentation {i j : SimplexCategory} (f : i ⟶ j) :
    categoryBarMap (R := R) (C := C) f ≫ categoryBarAugmentation i.len =
      categoryBarAugmentation j.len := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (categoryBarAugmentation (R := R) i.len).app X
      ((categoryBarMap f).app X (ModuleCat.freeMk ⟨s, g⟩)) = _
  simp [categoryBarMap, categoryBarAugmentation, categoryBarDesc, constantCoefficient]
  rfl

variable (R C)

/-- The unnormalized free-representable simplicial bar diagram. -/
def categoryBarSimplicial : SimplicialObject (CoefficientCategory R C) where
  obj i := categoryBarTerm R C i.unop.len
  map f := categoryBarMap f.unop
  map_id i := categoryBarMap_id i.unop
  map_comp f g := categoryBarMap_comp g.unop f.unop

/-- The augmented simplicial bar diagram. -/
def categoryBarAugmented : SimplicialObject.Augmented (CoefficientCategory R C) where
  left := categoryBarSimplicial R C
  right := constantCoefficient R C
  hom :=
    { app := fun i => categoryBarAugmentation i.unop.len
      naturality := by
        intro i j f
        change categoryBarMap f.unop ≫ categoryBarAugmentation _ =
          categoryBarAugmentation _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact categoryBarMap_augmentation f.unop }

/-- The associated chain complex; all its terms are proved projective. -/
def categoryBarComplex : ChainComplex (CoefficientCategory R C) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (CoefficientCategory R C)).obj
    (categoryBarSimplicial R C)

instance categoryBarComplex_projective (n : ℕ) :
    Projective ((categoryBarComplex R C).X n) :=
  categoryBarTerm_projective n

end Sharpness.Unconditional
