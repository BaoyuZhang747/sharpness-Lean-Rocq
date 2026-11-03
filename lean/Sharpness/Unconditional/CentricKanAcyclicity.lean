import Sharpness.Unconditional.CentricAcyclicityProducts
import Sharpness.Unconditional.CommaKanExactTerminal
import Sharpness.Unconditional.PuigProductDecomposition

/-! Exact right Kan extension carries slice coefficients to acyclic
coefficients on the original category. Finite representable product
decompositions supply the exactness, through actual terminal span families. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

/-- The right adjoint of an R-linear functor is R-linear. -/
theorem rightAdjoint_linear (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear R C]
    {D : Type w} [Category.{u} D] [Preadditive D] [Linear R D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [L.Linear R] [G.Additive]
    (adj : L ⊣ G) : G.Linear R where
  map_smul {X Y} r f := (adj.homEquiv _ _).symm.injective (by
    simp [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp])

variable (R : Type u) [CommRing R]
    {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Exact right Kan extension computes the same actual module-valued higher
limits as the source coefficient. -/
def higherLimitRanIso (L : C ⥤ D)
    [(L.op.ran (H := ModuleCat.{u} R)).PreservesEpimorphisms]
    (N : CoefficientCategory R C) (n : ℕ) :
    higherLimit N n ≅ higherLimit (L.op.ran.obj N) n := by
  let F := restrictionCoefficientFunctor R L
  let G := L.op.ran (H := ModuleCat.{u} R)
  let adj : F ⊣ G := L.op.ranAdjunction (ModuleCat.{u} R)
  letI : G.Additive := adj.right_adjoint_additive
  letI : G.Linear R := rightAdjoint_linear R adj
  haveI : F.PreservesHomology := by
    dsimp [F, restrictionCoefficientFunctor]
    infer_instance
  exact extAdjunctionIso R adj (constantCoefficient R D) N n

/-- Exact right Kan extension along the slice projection produces an acyclic
coefficient on the original category. -/
theorem overRan_acyclic (P : C)
    [((Over.forget P).op.ran (H := ModuleCat.{u} R)).PreservesEpimorphisms]
    (N : CoefficientCategory R (Over P)) :
    Acyclic ((Over.forget P).op.ran.obj N) := by
  intro n hn
  exact IsZero.of_iso (Burnside.over_acyclic R P N n hn)
    (higherLimitRanIso R (Over.forget P) N n).symm

namespace ProductDecomposition

variable {P Q : C} (E : ProductDecomposition P Q)

/-- A product summand, viewed as a span in the actual comma category. -/
def terminalSpan (i : E.Index) : CostructuredArrow (Over.forget P) Q :=
  CostructuredArrow.mk (Y := Over.mk (E.left i)) (E.right i)

/-- Every span factors through a summand of the product decomposition. -/
def terminalSpanLift (X : CostructuredArrow (Over.forget P) Q) :
    Σ i, X ⟶ E.terminalSpan i := by
  let z := (E.homEquiv X.left.left).symm (X.left.hom, X.hom)
  have hz : E.homEquiv X.left.left z = (X.left.hom, X.hom) :=
    (E.homEquiv X.left.left).apply_symm_apply _
  refine ⟨z.1, CostructuredArrow.homMk (Over.homMk z.2 ?_) ?_⟩
  · exact congrArg Prod.fst hz
  · exact congrArg Prod.snd hz

/-- The representing summand and factorization arrow are both unique. -/
theorem terminalSpanFactorization_subsingleton
    (X : CostructuredArrow (Over.forget P) Q) :
    Subsingleton (Σ i, X ⟶ E.terminalSpan i) := by
  refine ⟨fun x y => ?_⟩
  rcases x with ⟨i, f⟩
  rcases y with ⟨j, g⟩
  have h : (⟨i, f.left.left⟩ : Σ i, X.left.left ⟶ E.apex i) =
      ⟨j, g.left.left⟩ := by
    apply (E.homEquiv X.left.left).injective
    apply Prod.ext
    · exact f.left.w.trans g.left.w.symm
    · exact f.w.trans g.w.symm
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hfg : f.left.left = g.left.left := by simpa only [Sigma.mk.injEq, heq_eq_eq,
    true_and] using h
  congr 1
  apply CostructuredArrow.hom_ext
  exact CostructuredArrow.hom_ext _ _ hfg

/-- The product decomposition is exactly the terminal-family condition for
pointwise right Kan extension along the slice projection. -/
@[reducible] def terminalSpanFamilyUnique (X : CostructuredArrow (Over.forget P) Q) :
    Unique (Σ i, X ⟶ E.terminalSpan i) where
  default := E.terminalSpanLift X
  uniq _ := (E.terminalSpanFactorization_subsingleton X).elim _ _

end ProductDecomposition

/-- Representable product decompositions make right Kan extension from the
slice preserve epimorphisms. -/
theorem overRan_preservesEpimorphisms (P : C)
    (E : ∀ Q : C, ProductDecomposition P Q) :
    ((Over.forget P).op.ran (H := ModuleCat.{u} R)).PreservesEpimorphisms :=
  ran_op_preservesEpimorphisms_of_unique_terminal_family (Over.forget P) R
    (fun Q => (E Q).Index) (fun Q => (E Q).terminalSpan)
    (fun Q X => (E Q).terminalSpanFamilyUnique X)

/-- Any coefficient on the slice gives an acyclic coefficient on the base
once products of representables decompose into representable summands. -/
theorem overRan_acyclic_of_productDecomposition (P : C)
    (E : ∀ Q : C, ProductDecomposition P Q)
    (N : CoefficientCategory R (Over P)) :
    Acyclic ((Over.forget P).op.ran.obj N) := by
  letI := overRan_preservesEpimorphisms R P E
  exact overRan_acyclic R P N

/-- The actual pointwise product formula for the acyclic coefficient. -/
def overRanObjIsoProduct (P Q : C) (E : ProductDecomposition P Q)
    (N : CoefficientCategory R (Over P)) :
    (((Over.forget P).op.ran.obj N).obj (op Q)) ≅
      ∏ᶜ (fun i : E.Index => N.obj (op (Over.mk (E.left i)))) := by
  letI := oppositeTerminalFamily_initial (Over.forget P) Q E.terminalSpan
    E.terminalSpanFamilyUnique
  exact ranObjIsoProduct R (Over.forget P).op (op Q)
    (oppositeTerminalFamily (Over.forget P) Q E.terminalSpan) N

@[reassoc]
theorem overRanObjIsoProduct_hom_π (P Q : C) (E : ProductDecomposition P Q)
    (N : CoefficientCategory R (Over P)) (i : E.Index) :
    (overRanObjIsoProduct R P Q E N).hom ≫ Pi.π _ i =
      ((Over.forget P).op.ran.obj N).map (E.right i).op ≫
        ((Over.forget P).op.ranCounit.app N).app (op (Over.mk (E.left i))) := by
  letI := oppositeTerminalFamily_initial (Over.forget P) Q E.terminalSpan
    E.terminalSpanFamilyUnique
  exact ranObjIsoProduct_hom_π R (Over.forget P).op (op Q)
    (oppositeTerminalFamily (Over.forget P) Q E.terminalSpan) N i

/-- The pull map into the acyclic product coefficient is the unit of the
actual restriction/right-Kan adjunction. -/
def overRanPullMap (P : C) (M : CoefficientCategory R C) :
    M ⟶ (Over.forget P).op.ran.obj ((Over.forget P).op ⋙ M) :=
  ((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M

/-- Each coordinate of the canonical pull map is precisely restriction
along the right leg of the corresponding product summand. -/
@[reassoc]
theorem overRanPullMap_coordinate (P Q : C) (E : ProductDecomposition P Q)
    (M : CoefficientCategory R C) (i : E.Index) :
    (overRanPullMap R P M).app (op Q) ≫
        (overRanObjIsoProduct R P Q E ((Over.forget P).op ⋙ M)).hom ≫ Pi.π _ i =
      M.map (E.right i).op := by
  rw [overRanObjIsoProduct_hom_π]
  change (((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M).app (op Q) ≫
      ((Over.forget P).op.ran.obj ((Over.forget P).op ⋙ M)).map (E.right i).op ≫ _ = _
  have h := (((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M).naturality
    (E.right i).op
  change M.map (E.right i).op ≫
      (((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M).app
        (op (E.apex i)) =
    (((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M).app (op Q) ≫
      ((Over.forget P).op.ran.obj ((Over.forget P).op ⋙ M)).map (E.right i).op at h
  rw [← Category.assoc, ← h, Category.assoc]
  have hc := (Over.forget P).op.ranCounit_app_app_ranAdjunction_unit_app_app M
    (op (Over.mk (E.left i)))
  change (((Over.forget P).op.ranAdjunction (ModuleCat.{u} R)).unit.app M).app
      (op (E.apex i)) ≫
      ((Over.forget P).op.ranCounit.app ((Over.forget P).op ⋙ M)).app
        (op (Over.mk (E.left i))) = 𝟙 _ at hc
  rw [hc]
  exact Category.comp_id (M.map (E.right i).op)

end Sharpness
