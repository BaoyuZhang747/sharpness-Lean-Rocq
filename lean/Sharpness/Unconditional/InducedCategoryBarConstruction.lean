import Sharpness.CoefficientCochainFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
The free-representable bar construction induced along an actual functor.
Its degree `n` basis at `X` consists of a string `s` and an arrow from `X`
to the image of the first object of `s`. The linear Yoneda correspondence identifies maps
out of this diagram with the explicit restricted coefficient cochains already used in
the project. No bar-comparison theorem is assumed in this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable (R : Type u) [CommRing R] {C D : Type u} [Category.{u} C] [Category.{u} D]
  (q : C ⥤ D)

/-- The representable generators of the unnormalized bar term. -/
abbrev inducedCategoryBarBasis (n : ℕ) (X : Dᵒᵖ) :=
  Σ s : ComposableArrows C n, X.unop ⟶ q.obj (chainHead s)

/-- The free module on all strings starting after the evaluation object. -/
abbrev inducedCategoryBarTerm (n : ℕ) : CoefficientCategory R D where
  obj X := (ModuleCat.free R).obj (inducedCategoryBarBasis q n X)
  map {X Y} f := (ModuleCat.free R).map
    (↾fun b => ⟨b.1, f.unop ≫ b.2⟩ : inducedCategoryBarBasis q n X ⟶ inducedCategoryBarBasis q n Y)
  map_id X := by
    apply ModuleCat.free_hom_ext
    intro b
    simp
  map_comp f g := by
    apply ModuleCat.free_hom_ext
    intro b
    simp [Category.assoc]

variable {R q}

@[simp]
theorem inducedCategoryBarTerm_map_freeMk {n : ℕ} {X Y : Dᵒᵖ} (f : X ⟶ Y)
    (s : ComposableArrows C n) (g : X.unop ⟶ q.obj (chainHead s)) :
    (inducedCategoryBarTerm R q n).map f (ModuleCat.freeMk ⟨s, g⟩) =
      ModuleCat.freeMk ⟨s, f.unop ≫ g⟩ :=
  ModuleCat.free_map_apply _ _

/-- A map from a bar term is specified by one element for each string. -/
def inducedCategoryBarDesc {n : ℕ} (M : CoefficientCategory R D)
    (x : ∀ s : ComposableArrows C n, M.obj (op (q.obj (chainHead s)))) :
    inducedCategoryBarTerm R q n ⟶ M where
  app X := ModuleCat.freeDesc (↾fun b => M.map b.2.op (x b.1))
  naturality {X Y} f := by
    apply ModuleCat.free_hom_ext
    rintro ⟨s, g⟩
    change (ModuleCat.freeDesc (↾fun b : inducedCategoryBarBasis q n Y => M.map b.2.op (x b.1)))
        ((inducedCategoryBarTerm R q n).map f (ModuleCat.freeMk ⟨s, g⟩)) =
      M.map f ((ModuleCat.freeDesc (↾fun b : inducedCategoryBarBasis q n X => M.map b.2.op (x b.1)))
        (ModuleCat.freeMk ⟨s, g⟩))
    simp [op_comp, Functor.map_comp]

@[simp]
theorem inducedCategoryBarDesc_freeMk {n : ℕ} (M : CoefficientCategory R D)
    (x : ∀ s : ComposableArrows C n, M.obj (op (q.obj (chainHead s))))
    (X : Dᵒᵖ) (s : ComposableArrows C n) (g : X.unop ⟶ q.obj (chainHead s)) :
    (inducedCategoryBarDesc M x).app X (ModuleCat.freeMk ⟨s, g⟩) = M.map g.op (x s) :=
  ModuleCat.freeDesc_apply _ _

/-- The linear Yoneda correspondence for the bar term, including infinite
sets of strings (the domain is a coproduct and the codomain a product). -/
def inducedCategoryBarHomEquiv (n : ℕ) (M : CoefficientCategory R D) :
    (inducedCategoryBarTerm R q n ⟶ M) ≃ₗ[R]
      (∀ s : ComposableArrows C n, M.obj (op (q.obj (chainHead s)))) where
  toFun α s := α.app (op (q.obj (chainHead s))) (ModuleCat.freeMk ⟨s, 𝟙 _⟩)
  invFun := inducedCategoryBarDesc M
  left_inv α := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.free_hom_ext
    intro b
    rcases b with ⟨s, g⟩
    have h := congrArg (fun t => t (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) (α.naturality g.op)
    change α.app X ((inducedCategoryBarTerm R q n).map g.op (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) =
      M.map g.op (α.app _ (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) at h
    erw [inducedCategoryBarDesc_freeMk]
    simpa using h.symm
  right_inv x := by
    funext s
    simp [inducedCategoryBarDesc]
  map_add' α β := rfl
  map_smul' a α := rfl

@[simp]
theorem inducedCategoryBarHomEquiv_comp {n : ℕ} {M N : CoefficientCategory R D}
    (α : inducedCategoryBarTerm R q n ⟶ M) (f : M ⟶ N) (s : ComposableArrows C n) :
    inducedCategoryBarHomEquiv n N (α ≫ f) s =
      f.app (op (q.obj (chainHead s))) (inducedCategoryBarHomEquiv n M α s) := rfl

/-- Each bar term is projective, by lifting its string generators
independently through a pointwise epimorphism. -/
instance inducedCategoryBarTerm_projective (n : ℕ) : Projective (inducedCategoryBarTerm R q n) where
  factors {E M} f e he := by
    have hs (s : ComposableArrows C n) :
        ∃ x : E.obj (op (q.obj (chainHead s))),
          e.app _ x = inducedCategoryBarHomEquiv n M f s :=
      (ModuleCat.epi_iff_surjective (e.app _)).mp
        ((NatTrans.epi_iff_epi_app' (ModuleCat.{u} R) e).mp he _) _
    choose x hx using hs
    refine ⟨(inducedCategoryBarHomEquiv n E).symm x, ?_⟩
    apply (inducedCategoryBarHomEquiv n M).injective
    funext s
    simpa using hx s

/-- The simplicial map sends a generator to the restricted string and
composes its incoming arrow with the induced head arrow. -/
def inducedCategoryBarMap {i j : SimplexCategory} (f : i ⟶ j) :
    inducedCategoryBarTerm R q j.len ⟶ inducedCategoryBarTerm R q i.len where
  app X := (ModuleCat.free R).map
    (↾fun b => ⟨restrictCategoryChain f b.1, b.2 ≫ q.map (categoryChainHeadArrow f b.1)⟩ :
      inducedCategoryBarBasis q j.len X ⟶ inducedCategoryBarBasis q i.len X)
  naturality {X Y} g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨s, h⟩
    change (ModuleCat.free R).map
      (↾fun b : inducedCategoryBarBasis q j.len Y =>
        (⟨restrictCategoryChain f b.1, b.2 ≫ q.map (categoryChainHeadArrow f b.1)⟩ : inducedCategoryBarBasis q i.len Y))
      ((inducedCategoryBarTerm R q j.len).map g
        (ModuleCat.freeMk ⟨s, h⟩)) =
      (inducedCategoryBarTerm R q i.len).map g ((ModuleCat.free R).map
        (↾fun b : inducedCategoryBarBasis q j.len X =>
          (⟨restrictCategoryChain f b.1, b.2 ≫ q.map (categoryChainHeadArrow f b.1)⟩ : inducedCategoryBarBasis q i.len X))
        (ModuleCat.freeMk ⟨s, h⟩))
    simp [Category.assoc]

@[simp]
theorem inducedCategoryBarMap_freeMk {i j : SimplexCategory} (f : i ⟶ j)
    (X : Dᵒᵖ) (s : ComposableArrows C j.len) (g : X.unop ⟶ q.obj (chainHead s)) :
    (inducedCategoryBarMap (R := R) f).app X (ModuleCat.freeMk ⟨s, g⟩) =
      ModuleCat.freeMk ⟨restrictCategoryChain f s, g ≫ q.map (categoryChainHeadArrow f s)⟩ :=
  ModuleCat.free_map_apply _ _

@[simp]
theorem inducedCategoryBarMap_id (i : SimplexCategory) :
    inducedCategoryBarMap (R := R) (q := q) (𝟙 i) = 𝟙 (inducedCategoryBarTerm R q i.len) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (inducedCategoryBarMap (R := R) (𝟙 i)).app X (ModuleCat.freeMk ⟨s, g⟩) =
    ModuleCat.freeMk ⟨s, g⟩
  simp [inducedCategoryBarMap, restrictCategoryChain_id, categoryChainHeadArrow_id]

@[simp]
theorem inducedCategoryBarMap_comp {i j k : SimplexCategory} (f : i ⟶ j) (g : j ⟶ k) :
    inducedCategoryBarMap (R := R) (q := q) (f ≫ g) = inducedCategoryBarMap g ≫ inducedCategoryBarMap f := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, h⟩
  change (inducedCategoryBarMap (R := R) (f ≫ g)).app X (ModuleCat.freeMk ⟨s, h⟩) =
    (inducedCategoryBarMap f).app X ((inducedCategoryBarMap g).app X (ModuleCat.freeMk ⟨s, h⟩))
  simp [inducedCategoryBarMap, restrictCategoryChain_comp, categoryChainHeadArrow_comp, Functor.map_comp, Category.assoc]

/-- The bar simplicial map induces precisely the already-defined coefficient
replacement map, including its first face involving coefficient transport. -/
theorem inducedCategoryBarHomEquiv_map {i j : SimplexCategory} (f : i ⟶ j)
    (M : CoefficientCategory R D) (α : inducedCategoryBarTerm R q i.len ⟶ M) :
    inducedCategoryBarHomEquiv j.len M (inducedCategoryBarMap f ≫ α) =
      coefficientReplacementMap (q.op ⋙ M) f (inducedCategoryBarHomEquiv i.len M α) := by
  funext s
  change α.app (op (q.obj (chainHead s)))
      ((inducedCategoryBarMap f).app _ (ModuleCat.freeMk ⟨s, 𝟙 _⟩)) =
    M.map (q.map (categoryChainHeadArrow f s)).op
      (α.app (op (q.obj (chainHead (restrictCategoryChain f s))))
        (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩))
  have h := congrArg
    (fun t => t (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩))
    (α.naturality (q.map (categoryChainHeadArrow f s)).op)
  change α.app (op (q.obj (chainHead s)))
      ((inducedCategoryBarTerm R q i.len).map (q.map (categoryChainHeadArrow f s)).op
        (ModuleCat.freeMk ⟨restrictCategoryChain f s, 𝟙 _⟩)) = _ at h
  simpa [inducedCategoryBarMap] using h

/-- Every bar generator augments to `1` in the constant diagram. -/
def inducedCategoryBarAugmentation (n : ℕ) : inducedCategoryBarTerm R q n ⟶ constantCoefficient R D :=
  inducedCategoryBarDesc (constantCoefficient R D) (fun _ => (1 : R))

@[simp]
theorem inducedCategoryBarAugmentation_freeMk (n : ℕ) (X : Dᵒᵖ)
    (s : ComposableArrows C n) (g : X.unop ⟶ q.obj (chainHead s)) :
    (inducedCategoryBarAugmentation (R := R) n).app X (ModuleCat.freeMk ⟨s, g⟩) = (1 : R) :=
  inducedCategoryBarDesc_freeMk _ _ _ _ _

@[simp]
theorem inducedCategoryBarMap_augmentation {i j : SimplexCategory} (f : i ⟶ j) :
    inducedCategoryBarMap (R := R) (q := q) f ≫ inducedCategoryBarAugmentation i.len =
      inducedCategoryBarAugmentation j.len := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  change (inducedCategoryBarAugmentation (R := R) i.len).app X
      ((inducedCategoryBarMap f).app X (ModuleCat.freeMk ⟨s, g⟩)) = _
  simp [inducedCategoryBarMap, inducedCategoryBarAugmentation, inducedCategoryBarDesc, constantCoefficient]
  rfl

variable (R q)

/-- The unnormalized free-representable simplicial bar diagram. -/
def inducedCategoryBarSimplicial : SimplicialObject (CoefficientCategory R D) where
  obj i := inducedCategoryBarTerm R q i.unop.len
  map f := inducedCategoryBarMap f.unop
  map_id i := inducedCategoryBarMap_id i.unop
  map_comp f g := inducedCategoryBarMap_comp g.unop f.unop

/-- The augmented simplicial bar diagram. -/
def inducedCategoryBarAugmented : SimplicialObject.Augmented (CoefficientCategory R D) where
  left := inducedCategoryBarSimplicial R q
  right := constantCoefficient R D
  hom :=
    { app := fun i => inducedCategoryBarAugmentation i.unop.len
      naturality := by
        intro i j f
        change inducedCategoryBarMap f.unop ≫ inducedCategoryBarAugmentation _ =
          inducedCategoryBarAugmentation _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact inducedCategoryBarMap_augmentation f.unop }

/-- The associated chain complex; all its terms are proved projective. -/
def inducedCategoryBarComplex : ChainComplex (CoefficientCategory R D) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (CoefficientCategory R D)).obj
    (inducedCategoryBarSimplicial R q)

instance inducedCategoryBarComplex_projective (n : ℕ) :
    Projective ((inducedCategoryBarComplex R q).X n) :=
  inducedCategoryBarTerm_projective n

end Sharpness.Unconditional
