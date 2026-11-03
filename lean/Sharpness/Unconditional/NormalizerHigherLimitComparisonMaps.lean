import Sharpness.Unconditional.GroupCohomologyInner
import Sharpness.Unconditional.NormalizerSubdivisionCommaAdjunction

/-! Native group-cohomology maps attached to the actual comma reflections.
The maps are induced by group homomorphisms. Their coherence follows from
the adjunction transformations and the proved invariance under inner
automorphisms; no topological comparison or vanishing premise is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory Opposite
variable {R G H K : Type u} [CommRing R] [Group G] [Group H] [Group K]
    {A : ModuleCat.{u} R}

/-- The native pullback belonging to a functor of one-object group categories. -/
def functorPull (T : SingleObj G ⥤ SingleObj H) (n : ℕ) :
    value R H A n ⟶ value R G A n :=
  pull ((SingleObj.mapHom G H).symm T) n

theorem functorPull_id (n : ℕ) :
    functorPull (R := R) (A := A) (𝟭 (SingleObj G)) n = 𝟙 _ :=
  pull_id n

theorem functorPull_comp (T : SingleObj G ⥤ SingleObj H)
    (U : SingleObj H ⥤ SingleObj K) (n : ℕ) :
    functorPull (R := R) (A := A) (T ⋙ U) n =
      functorPull U n ≫ functorPull T n :=
  pull_comp ((SingleObj.mapHom G H).symm T) ((SingleObj.mapHom H K).symm U) n

/-- A natural transformation conjugates the underlying group homomorphisms,
so it gives equality of their native cohomology pullbacks. -/
theorem functorPull_eq_of_natTrans {T U : SingleObj G ⥤ SingleObj H}
    (α : T ⟶ U) (n : ℕ) :
    functorPull (R := R) (A := A) T n = functorPull U n := by
  let a : H := α.app (SingleObj.star G)
  have h : (SingleObj.mapHom G H).symm U =
      (MulAut.conj a).toMonoidHom.comp ((SingleObj.mapHom G H).symm T) := by
    ext g
    have hg := α.naturality (X := SingleObj.star G) (Y := SingleObj.star G) g
    change a * T.map g = U.map g * a at hg
    change U.map g = a * T.map g * a⁻¹
    rw [hg, mul_assoc, mul_inv_cancel, mul_one]
  dsimp only [functorPull]
  rw [h, pull_comp, pull_inner, Category.id_comp]

end Sharpness.OrdinaryCohomology

namespace Sharpness.NormalizerReflection
open CategoryTheory Opposite
variable {D : Type u} [Category.{u} D] (K : D ⥤ Cat.{u,u})
    (G : D → Type u) [∀ d, Group (G d)]
    (J : ∀ d, SingleObj (G d) ⥤ K.obj d)
    (P : ∀ d, K.obj d ⥤ SingleObj (G d))
    (adj : ∀ d, P d ⊣ J d)

/-- The actual group functor determined by an indexing arrow and the two
comma comparisons. It need not compose strictly before cohomology. -/
def arrowFunctor {d e : D} (f : d ⟶ e) : SingleObj (G d) ⥤ SingleObj (G e) :=
  J d ⋙ (K.map f).toFunctor ⋙ P e

/-- Native chain-automorphism cohomology, with its genuine group pullbacks.
Adjunction units remove the middle reflection in a composite. -/
def coefficient (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ) :
    Dᵒᵖ ⥤ ModuleCat.{u} R where
  obj d := OrdinaryCohomology.value R (G d.unop) A n
  map f := OrdinaryCohomology.functorPull (arrowFunctor K G J P f.unop) n
  map_id d := by
    have hid : arrowFunctor K G J P (𝟙 d.unop) = J d.unop ⋙ P d.unop := by
      simp only [arrowFunctor, K.map_id, Cat.Hom.id_toFunctor]
      rfl
    rw [unop_id, hid, OrdinaryCohomology.functorPull_eq_of_natTrans (adj d.unop).counit,
      OrdinaryCohomology.functorPull_id]
  map_comp {d e t} f g := by
    have hc : arrowFunctor K G J P (g.unop ≫ f.unop) =
        J t.unop ⋙ (K.map g.unop).toFunctor ⋙ (K.map f.unop).toFunctor ⋙ P d.unop := by
      simp only [arrowFunctor, K.map_comp, Cat.Hom.comp_toFunctor]
      rfl
    rw [unop_comp, hc]
    let η := Functor.whiskerLeft (J t.unop ⋙ (K.map g.unop).toFunctor)
      (Functor.whiskerRight (adj e.unop).unit ((K.map f.unop).toFunctor ⋙ P d.unop))
    have he := OrdinaryCohomology.functorPull_eq_of_natTrans
      (R := R) (A := A) η n
    exact he.trans (OrdinaryCohomology.functorPull_comp
      (arrowFunctor K G J P g.unop) (arrowFunctor K G J P f.unop) n)

end Sharpness.NormalizerReflection

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- A representative is chosen only for the values of the native diagram. -/
def normalizerRepresentative (d : F.NormalizerCategory) : F.CentricChain := Quotient.out d

omit [Finite S] in
theorem normalizerRepresentative_class (d : F.NormalizerCategory) :
    F.normalizerClass ((normalizerRepresentative (F := F) d)) = d := Quotient.out_eq d

def normalizerRepresentativeComparison (d : F.NormalizerCategory) :
    SingleObj (L.ChainAut ((normalizerRepresentative (F := F) d))) ⥤
      CostructuredArrow L.normalizerSubdivisionProjection d :=
  Eq.ndrec (motive := fun e =>
    SingleObj (L.ChainAut (normalizerRepresentative (F := F) d)) ⥤
      CostructuredArrow L.normalizerSubdivisionProjection e)
    (L.normalizerSubdivisionChainComparison (normalizerRepresentative (F := F) d))
    (normalizerRepresentative_class d)

def normalizerRepresentativeReflection (d : F.NormalizerCategory) :
    CostructuredArrow L.normalizerSubdivisionProjection d ⥤
      SingleObj (L.ChainAut ((normalizerRepresentative (F := F) d))) :=
  Eq.ndrec (motive := fun e =>
    CostructuredArrow L.normalizerSubdivisionProjection e ⥤
      SingleObj (L.ChainAut (normalizerRepresentative (F := F) d)))
    (L.normalizerCommaReflection (normalizerRepresentative (F := F) d))
    (normalizerRepresentative_class d)

def normalizerRepresentativeAdjunction (d : F.NormalizerCategory) :
    L.normalizerRepresentativeReflection d ⊣ L.normalizerRepresentativeComparison d := by
  unfold normalizerRepresentativeReflection normalizerRepresentativeComparison
  have aux (σ : F.CentricChain) (e : F.NormalizerCategory)
      (h : F.normalizerClass σ = e) :
      (h ▸ L.normalizerCommaReflection σ) ⊣
        (h ▸ L.normalizerSubdivisionChainComparison σ) := by
    subst e
    exact L.normalizerCommaAdjunction σ
  exact aux _ _ _

def normalizerOrdinaryDiagram (R : Type u) [CommRing R]
    (A : ModuleCat.{u} R) (n : ℕ) :
    F.NormalizerCategoryᵒᵖ ⥤ ModuleCat.{u} R :=
  NormalizerReflection.coefficient (CostructuredArrow.functor L.normalizerSubdivisionProjection)
    (fun d => L.ChainAut ((normalizerRepresentative (F := F) d)))
    L.normalizerRepresentativeComparison L.normalizerRepresentativeReflection
    L.normalizerRepresentativeAdjunction R A n

end Sharpness.FusionSystem.CentricLinkingSystem
