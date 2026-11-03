import Sharpness.CategoryCochainReplacement

/-! Explicit differentials and totalization for the constructed replacement.
The identities are the native bicomplex identities, with no additional
commutation or square-zero assumptions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

theorem cochainReplacementBicomplex_term (i n : ℕ) :
    ((cochainReplacementBicomplex D).X i).X n =
      ModuleCat.of R (∀ s : ComposableArrows C i, (D.obj (op (chainHead s))).X n) := rfl

theorem cochainReplacementBicomplex_vertical (i n : ℕ)
    (x : ((cochainReplacementBicomplex D).X i).X n) (s : ComposableArrows C i) :
    ((cochainReplacementBicomplex D).X i).d n (n+1) x s =
      (D.obj (op (chainHead s))).d n (n+1) (x s) := by
  change (productCochains _).d n (n+1) x s = _
  dsimp only [productCochains]
  rw [CochainComplex.of_d]
  rfl

theorem cochainReplacementBicomplex_horizontal (i : ℕ) :
    (cochainReplacementBicomplex D).d i (i+1) =
      ∑ j : Fin (i+2), (-1 : ℤ)^j.val • cochainReplacementMap D (SimplexCategory.δ j) := by
  dsimp only [cochainReplacementBicomplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

theorem cochainReplacementBicomplex_comm (i n : ℕ) :
    ((cochainReplacementBicomplex D).d i (i+1)).f n ≫
        ((cochainReplacementBicomplex D).X (i+1)).d n (n+1) =
      ((cochainReplacementBicomplex D).X i).d n (n+1) ≫
        ((cochainReplacementBicomplex D).d i (i+1)).f (n+1) :=
  HomologicalComplex₂.d_comm _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem cochainReplacementTotal_d (i n : ℕ) :
    (cochainReplacementBicomplex D).ιTotal (ComplexShape.up ℕ) i n (i+n) rfl ≫
        (cochainReplacementTotal D).d (i+n) (i+n+1) =
      ((cochainReplacementBicomplex D).d i (i+1)).f n ≫
          (cochainReplacementBicomplex D).ιTotal (ComplexShape.up ℕ)
            (i+1) n (i+n+1) (by change i+1+n=i+n+1; omega) +
        (-1 : ℤˣ)^i •
          (((cochainReplacementBicomplex D).X i).d n (n+1) ≫
            (cochainReplacementBicomplex D).ιTotal (ComplexShape.up ℕ)
              i (n+1) (i+n+1) (by change i+(n+1)=i+n+1; omega)) := by
  dsimp only [cochainReplacementTotal]
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) n
      (i+n+1) (by change i+1+n=i+n+1; omega),
    HomologicalComplex₂.d₂_eq _ _ i (show (ComplexShape.up ℕ).Rel n (n+1) from rfl)
      (i+n+1) (by change i+(n+1)=i+n+1; omega)]
  simp only [cochainNatTotalHorizontalSign, cochainNatTotalVerticalSign, one_smul]

end Sharpness
