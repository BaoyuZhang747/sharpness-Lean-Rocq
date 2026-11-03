import Sharpness.Unconditional.GroupCohomologyInner
import Sharpness.Unconditional.GroupCohomologyResolutionComparison

/-! Inner conjugation on group cohomology with arbitrary representations.
The coefficient correction is the actual action by the inverse conjugating
element. This is the naturality needed for the cohomological Mackey square. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Finsupp
variable {R G : Type u} [CommRing R] [Group G]

/-- Conjugating the group action back by its actual inverse action. -/
def conjugationCoefficientHom (V : Rep.{u} R G) (g : G) :
    Rep.res (MulAut.conj g).toMonoidHom V ⟶ V :=
  Rep.ofHom ⟨V.ρ g⁻¹, fun h => by
    change V.ρ g⁻¹ * V.ρ ((MulAut.conj g) h) = V.ρ h * V.ρ g⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjugationCoefficientHom_apply (V : Rep.{u} R G) (g : G) (a : V) :
    (conjugationCoefficientHom V g).hom a = V.ρ g⁻¹ a := rfl

theorem homComplexPrecomp_id (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    homComplexPrecomp V (𝟙 X) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Category.id_comp a

theorem inner_cochain_comparison_coefficients (V : Rep.{u} R G) (g : G) :
    groupCohomology.cochainsMap (MulAut.conj g).toMonoidHom
        (conjugationCoefficientHom V g) ≫
        (groupCohomology.inhomogeneousCochainsIso V).hom =
      (groupCohomology.inhomogeneousCochainsIso V).hom ≫
        homComplexPrecomp V (innerBarChain g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Rep.free_ext
  intro y
  change (Rep.freeLift R G V (fun z => V.ρ g⁻¹ (x ((MulAut.conj g) ∘ z)))).hom
      (single y (single 1 1)) =
    (Rep.freeLift R G V x).hom
      ((innerBarComponent g n).hom (single y (single 1 1)))
  simp [Rep.freeLift, innerBarComponent, Representation.freeLift_single_single]

/-- Corrected inner conjugation is the identity on native cohomology,
for every coefficient representation and every degree. -/
theorem map_inner_coefficients (V : Rep.{u} R G) (g : G) (n : ℕ) :
    groupCohomology.map (MulAut.conj g).toMonoidHom
      (conjugationCoefficientHom V g) n = 𝟙 _ := by
  let e := groupCohomology.inhomogeneousCochainsIso V
  apply (cancel_mono (HomologicalComplex.homologyMap e.hom n)).mp
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (inner_cochain_comparison_coefficients V g)
  have hi := homComplexPrecomp_homology_eq V (innerBarHomotopy (R := R) g) n
  rw [homComplexPrecomp_id, HomologicalComplex.homologyMap_id] at hi
  simpa only [groupCohomology.map, e, HomologicalComplex.homologyMap_comp,
    hi, Category.comp_id, Category.id_comp] using h

end Sharpness.OrdinaryCohomology
