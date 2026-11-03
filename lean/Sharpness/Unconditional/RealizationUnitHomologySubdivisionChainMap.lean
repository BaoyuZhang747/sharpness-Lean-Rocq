import Sharpness.Unconditional.RealizationUnitHomologySubdivisionOuterFaces
import Sharpness.Unconditional.RealizationUnitHomologySubdivisionNaturality
import Sharpness.Unconditional.RealizationSubdivisionFaces
import Sharpness.Unconditional.RealizationSubdivisionOuterFaces

/-! Boundary commutation for the actual signed barycentric subdivision. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial Opposite
open scoped BigOperators
variable (R : Type u) [CommRing R] (X : TopCat.{u})

theorem subdivision_boundary_sum (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    (∑ p : Equiv.Perm (Fin (n + 2)), (p.sign : ℤ) •
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          ((TopCat.toSSet.obj X).δ j (singularBarycentricCell σ p))) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      ∑ q : Equiv.Perm (Fin (n + 1)), (q.sign : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          (singularBarycentricCell ((TopCat.toSSet.obj X).δ i σ) q) := by
  classical
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  have hz : (∑ j : Fin (n + 1), ∑ p : Equiv.Perm (Fin (n + 2)),
      (p.sign : ℤ) • (-1 : ℤ) ^ j.castSucc.val •
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          ((TopCat.toSSet.obj X).δ j.castSucc (singularBarycentricCell σ p))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply subdivision_internal_face_sum_zero j
    intro p
    simp only [subdivisionAdjacentPair, singularBarycentricCell_internal_face]
  rw [hz, zero_add]
  simp only [Fin.val_last, smul_smul]
  rw [subdivision_outer_face_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro q _
  rw [singularBarycentricCell_outer_face σ _ q i
    (subdivisionOuterAssemble_castSucc i q)]

/-- The actual signed subdivision commutes with the native singular boundary. -/
theorem subdivisionDegree_boundary (n : ℕ) :
    subdivisionDegree R X (n + 1) ≫
        ((SingularCohomology.chainsFunctor R).obj X).d (n + 1) n =
      ((SingularCohomology.chainsFunctor R).obj X).d (n + 1) n ≫
        subdivisionDegree R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have hd (τ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) τ ≫
        ((SingularCohomology.chainsFunctor R).obj X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R)
          ((TopCat.toSSet.obj X).δ i τ) :=
        SSet.ιChainComplex_d (TopCat.toSSet.obj X) (ModuleCat.of R R) τ
  rw [subdivisionDegree_generator_assoc]
  change _ = (TopCat.toSSet.obj X).ιChainComplex σ ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).d (n + 1) n ≫ _
  rw [SSet.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    hd, subdivisionDegree_generator]
  exact subdivision_boundary_sum R X n σ

/-- Actual subdivision as a chain map, after the boundary proof above. -/
def subdivisionChainMap :
    (SingularCohomology.chainsFunctor R).obj X ⟶
      (SingularCohomology.chainsFunctor R).obj X where
  f := subdivisionDegree R X
  comm' i j hij := by
    have h : i = j + 1 := hij.symm
    subst i
    exact subdivisionDegree_boundary R X j

/-- Subdivision is a genuine natural transformation of singular-chain functors. -/
def subdivisionNatTrans :
    SingularCohomology.chainsFunctor R ⟶ SingularCohomology.chainsFunctor R where
  app X := subdivisionChainMap R X
  naturality {X Y} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact subdivisionDegree_naturality R f n

end Sharpness.RealizationUnitHomology
