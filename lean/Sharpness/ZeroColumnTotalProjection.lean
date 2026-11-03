import Sharpness.ZeroColumnTotalMap

/-! Projection to column zero is an actual cochain map of the total
complex. The proof checks every total summand, using first-quadrant
support and the actual signed total differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalSummandProjectionAt_other (p q n i j : ℕ) (hp : p+q=n) (hij : i+j=n) (hi : i≠p) :
    K.ιTotal (ComplexShape.up ℕ) i j n hij ≫ totalSummandProjectionAt K p q n hp = 0 := by
  classical
  dsimp only [totalSummandProjectionAt]
  rw [HomologicalComplex₂.ι_totalDesc, dif_neg (fun h => hi h.1)]

set_option backward.isDefEq.respectTransparency false in
theorem zeroColumnTotalProjection_d (n : ℕ) :
    totalSummandProjectionAt K 0 n n (by omega) ≫ (K.X 0).d n (n+1) =
      (K.total (ComplexShape.up ℕ)).d n (n+1) ≫ totalSummandProjectionAt K 0 (n+1) (n+1) (by omega) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  change i+j=n at h
  have hij : i+j=n := h
  by_cases hi : i=0
  · subst i
    have hj : j=n := by omega
    subst j
    have h₀ := totalSummandProjectionAt_inclusion K 0 n n (by omega)
    have h₁ := totalSummandProjectionAt_other K 0 (n+1) (n+1) 1 n (by omega) (by omega) (by omega)
    have h₂ := totalSummandProjectionAt_inclusion K 0 (n+1) (n+1) (by omega)
    calc
      _ = (K.X 0).d n (n+1) := by rw [← Category.assoc, h₀, Category.id_comp]
      _ = ((K.d 0 1).f n ≫ K.ιTotal (ComplexShape.up ℕ) 1 n (n+1) (by change 1+n=n+1; omega) +
          (K.X 0).d n (n+1) ≫ K.ιTotal (ComplexShape.up ℕ) 0 (n+1) (n+1)
            (by change 0+(n+1)=n+1; omega)) ≫
          totalSummandProjectionAt K 0 (n+1) (n+1) (by omega) := by
        simp only [Preadditive.add_comp, Category.assoc, h₁, h₂, comp_zero, Category.comp_id, zero_add]
      _ = _ := (congrArg (fun t => t ≫ totalSummandProjectionAt K 0 (n+1) (n+1) (by omega))
        (zeroColumnTotal_d K n).symm).trans (Category.assoc _ _ _)
  · subst n
    have h₀ := totalSummandProjectionAt_other K 0 (i+j) (i+j) i j (by omega) rfl hi
    have h₁ := totalSummandProjectionAt_other K 0 (i+j+1) (i+j+1) (i+1) j (by omega) (by omega) (by omega)
    have h₂ := totalSummandProjectionAt_other K 0 (i+j+1) (i+j+1) i (j+1) (by omega) (by omega) hi
    calc
      _ = 0 := by rw [← Category.assoc, h₀, zero_comp]
      _ = ((K.d i (i+1)).f j ≫ K.ιTotal (ComplexShape.up ℕ) (i+1) j (i+j+1)
            (by change i+1+j=i+j+1; omega) +
          (-1 : ℤˣ)^i • ((K.X i).d j (j+1) ≫ K.ιTotal (ComplexShape.up ℕ) i (j+1) (i+j+1)
            (by change i+(j+1)=i+j+1; omega))) ≫
          totalSummandProjectionAt K 0 (i+j+1) (i+j+1) (by omega) := by
        simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
          h₁, h₂, comp_zero, smul_zero, add_zero]
      _ = _ := (congrArg (fun t => t ≫ totalSummandProjectionAt K 0 (i+j+1) (i+j+1) (by omega))
        (cochainNatBicomplexTotal_d K i j).symm).trans (Category.assoc _ _ _)

def zeroColumnTotalProjection : K.total (ComplexShape.up ℕ) ⟶ K.X 0 :=
  CochainComplex.ofHom (fun n => totalSummandProjectionAt K 0 n n (by omega))
    (zeroColumnTotalProjection_d K)

end Sharpness
