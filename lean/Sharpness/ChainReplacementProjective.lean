import Sharpness.CategoryChainReplacementTotal
import Sharpness.ModuleDirectSumProjective
import Sharpness.NatTotalIndex

/-! Pointwise projective diagrams give degreewise projective actual
replacement bicomplexes and their native direct-sum total complexes. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ)
    [∀ X n, Projective ((D.obj X).X n)]

theorem chainReplacementBicomplex_projective (p q : ℕ) :
    Projective (((chainReplacementBicomplex D).X p).X q) := by
  change Projective (moduleDirectSum (fun s : ComposableArrows C p =>
    (D.obj (chainHead s)).X q))
  exact moduleDirectSum_projective _

set_option backward.isDefEq.respectTransparency false in
theorem chainReplacementTotal_projective (n : ℕ) :
    Projective ((chainReplacementTotal D).X n) := by
  letI : ∀ p q, Projective (((chainReplacementBicomplex D).X p).X q) :=
    chainReplacementBicomplex_projective D
  constructor
  intro E X f e he
  refine ⟨(chainReplacementBicomplex D).totalDesc (fun p q h =>
    Projective.factorThru
      ((chainReplacementBicomplex D).ιTotal (ComplexShape.down ℕ) p q n h ≫ f) e), ?_⟩
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc, Projective.factorThru_comp]

end Sharpness
