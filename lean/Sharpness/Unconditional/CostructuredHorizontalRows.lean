import Sharpness.Unconditional.CostructuredHorizontalRowsStrings

/-! An actual horizontal row of the comma-nerve replacement is the
disjoint union, indexed by C-strings, of nerves of the appropriate coslices.
The forward and inverse maps are explicit, and the isomorphism is natural
for every simplicial operator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredHorizontalRow (q : ℕ) : SSet.{u} :=
  (simplicialSetReplacement (costructuredNerveDiagram T)).flip.obj (op (.mk q))

def costructuredHorizontalRowModel (q : ℕ) : SSet.{u} where
  obj p := Σ c : ComposableArrows C q,
    (CategoryTheory.nerve (Under (T.obj (c.obj (Fin.last q))))).obj p
  map f := ↾fun x => ⟨x.1,
    (CategoryTheory.nerve (Under (T.obj (x.1.obj (Fin.last q))))).map f x.2⟩
  map_id p := by
    apply ConcreteCategory.ext_apply
    rintro ⟨c, x⟩
    rfl
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    rintro ⟨c, x⟩
    rfl

/-- Keep the C-string and extend the last comma arrow along the D-string. -/
def costructuredHorizontalRowEncode (q : ℕ) (p : SimplexCategoryᵒᵖ)
    (z : (costructuredHorizontalRow T q).obj p) :
    (costructuredHorizontalRowModel T q).obj p :=
  ⟨z.2 ⋙ CostructuredArrow.proj T (chainHead z.1),
    underStringFromHead z.1 (z.2.obj (Fin.last q)).hom⟩

/-- Extend the first coslice arrow backwards along the fixed C-string. -/
def costructuredHorizontalRowDecode (q : ℕ) (p : SimplexCategoryᵒᵖ)
    (z : (costructuredHorizontalRowModel T q).obj p) :
    (costructuredHorizontalRow T q).obj p :=
  ⟨z.2 ⋙ Under.forget (T.obj (z.1.obj (Fin.last q))),
    costructuredStringFromLast T z.1 (z.2.obj 0).hom⟩

theorem costructuredHorizontalRow_decode_encode (q : ℕ) (p : SimplexCategoryᵒᵖ)
    (z : (costructuredHorizontalRow T q).obj p) :
    costructuredHorizontalRowDecode T q p (costructuredHorizontalRowEncode T q p z) = z := by
  rcases z with ⟨s, x⟩
  change (⟨s, costructuredStringFromLast T (x ⋙ CostructuredArrow.proj T (chainHead s))
    ((underStringFromHead s (x.obj (Fin.last q)).hom).obj 0).hom⟩ :
      (costructuredHorizontalRow T q).obj p) = ⟨s, x⟩
  rw [underStringFromHead_first]
  exact congrArg (fun y => (⟨s, y⟩ : (costructuredHorizontalRow T q).obj p))
    (costructuredStringFromLast_recover T x)

theorem costructuredHorizontalRow_encode_decode (q : ℕ) (p : SimplexCategoryᵒᵖ)
    (z : (costructuredHorizontalRowModel T q).obj p) :
    costructuredHorizontalRowEncode T q p (costructuredHorizontalRowDecode T q p z) = z := by
  rcases z with ⟨c, x⟩
  change (⟨c, underStringFromHead (x ⋙ Under.forget (T.obj (c.obj (Fin.last q))))
    (T.map (categoryStringTerminalArrow c (Fin.last q)) ≫ (x.obj 0).hom)⟩ :
      (costructuredHorizontalRowModel T q).obj p) = ⟨c, x⟩
  rw [categoryStringTerminalArrow_last, T.map_id, Category.id_comp]
  exact congrArg (fun y => (⟨c, y⟩ : (costructuredHorizontalRowModel T q).obj p))
    (underStringFromHead_recover x)

theorem costructuredHorizontalRowEncode_naturality (q : ℕ)
    {p r : SimplexCategoryᵒᵖ} (f : p ⟶ r) (z : (costructuredHorizontalRow T q).obj p) :
    costructuredHorizontalRowEncode T q r ((costructuredHorizontalRow T q).map f z) =
      (costructuredHorizontalRowModel T q).map f (costructuredHorizontalRowEncode T q p z) := by
  rcases z with ⟨s, x⟩
  change (⟨x ⋙ CostructuredArrow.proj T (chainHead s),
      underStringFromHead ((SimplexCategory.toCat.map f.unop).toFunctor ⋙ s)
        ((x.obj (Fin.last q)).hom ≫ categoryChainHeadArrow f.unop s)⟩ :
      (costructuredHorizontalRowModel T q).obj r) =
    ⟨x ⋙ CostructuredArrow.proj T (chainHead s),
      (SimplexCategory.toCat.map f.unop).toFunctor ⋙
        underStringFromHead s (x.obj (Fin.last q)).hom⟩
  exact congrArg (fun y => (⟨x ⋙ CostructuredArrow.proj T (chainHead s), y⟩ :
      (costructuredHorizontalRowModel T q).obj r))
    (underStringFromHead_restrict s (x.obj (Fin.last q)).hom
      (SimplexCategory.toCat.map f.unop).toFunctor)

/-- The genuine simplicial isomorphism of horizontal rows. -/
def costructuredHorizontalRowIso (q : ℕ) :
    costructuredHorizontalRow T q ≅ costructuredHorizontalRowModel T q :=
  NatIso.ofComponents (fun p =>
    { hom := ↾costructuredHorizontalRowEncode T q p
      inv := ↾costructuredHorizontalRowDecode T q p
      hom_inv_id := by
        apply ConcreteCategory.ext_apply
        exact costructuredHorizontalRow_decode_encode T q p
      inv_hom_id := by
        apply ConcreteCategory.ext_apply
        exact costructuredHorizontalRow_encode_decode T q p }) (by
    intro p r f
    apply ConcreteCategory.ext_apply
    exact costructuredHorizontalRowEncode_naturality T q f)

/-- The row augmentation is the actual projection to the C-string. -/
def costructuredHorizontalRowAugmentation (q : ℕ) :
    costructuredHorizontalRow T q ⟶
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C q) where
  app p := ↾fun z => z.2 ⋙ CostructuredArrow.proj T (chainHead z.1)
  naturality {_ _} f := rfl

def costructuredHorizontalRowModelProjection (q : ℕ) :
    costructuredHorizontalRowModel T q ⟶
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C q) where
  app p := ↾Sigma.fst
  naturality {_ _} f := rfl

theorem costructuredHorizontalRowIso_projection (q : ℕ) :
    (costructuredHorizontalRowIso T q).hom ≫ costructuredHorizontalRowModelProjection T q =
      costructuredHorizontalRowAugmentation T q := rfl

theorem costructuredHorizontalRowAugmentation_component (q : ℕ) (p : SimplexCategoryᵒᵖ) :
    (costructuredHorizontalRowAugmentation T q).app p =
      (simplicialReplacementColumnAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T) p.unop).app (op (.mk q)) := rfl

end Sharpness
