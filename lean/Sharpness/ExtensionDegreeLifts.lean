import Sharpness.ExtendCycleClasses

/-! Actual degreewise lifting through extension by zero commutes with
complex maps and differentials at specified embedded degrees. -/
set_option autoImplicit false
noncomputable section
universe u v t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c)

def extensionDegreeLift {M : C} (i : ι) (i' : ι') (hi : e.f i=i') (x : M ⟶ K.X i) :
    M ⟶ (K.extend e).X i' := x ≫ (K.extendXIso e hi).inv

theorem extensionDegreeLift_map {L : HomologicalComplex C c} (φ : K ⟶ L)
    {M : C} (i : ι) (i' : ι') (hi : e.f i=i') (x : M ⟶ K.X i) :
    extensionDegreeLift e K i i' hi x ≫ (HomologicalComplex.extendMap φ e).f i' =
      extensionDegreeLift e L i i' hi (x ≫ φ.f i) := by
  rw [extensionDegreeLift, Category.assoc, HomologicalComplex.extendMap_f φ e hi]
  simp only [extensionDegreeLift, Category.assoc, Iso.inv_hom_id_assoc]

theorem extensionDegreeLift_d {M : C} (i j : ι) (i' j' : ι')
    (hi : e.f i=i') (hj : e.f j=j') (x : M ⟶ K.X i) :
    extensionDegreeLift e K i i' hi x ≫ (K.extend e).d i' j' =
      extensionDegreeLift e K j j' hj (x ≫ K.d i j) := by
  rw [extensionDegreeLift, Category.assoc, K.extend_d_eq e hi hj]
  simp only [extensionDegreeLift, Category.assoc, Iso.inv_hom_id_assoc]

theorem extensionDegreeLift_closed {M : C} (i j : ι) (i' j' : ι')
    (hi : e.f i=i') (hj : e.f j=j') (x : M ⟶ K.X i) (hx : x ≫ K.d i j=0) :
    extensionDegreeLift e K i i' hi x ≫ (K.extend e).d i' j' = 0 := by
  rw [extensionDegreeLift_d e K i j i' j' hi hj x, hx, extensionDegreeLift, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem extensionDegreeLiftCycleClass {M : C} (i j : ι) (i' j' : ι')
    (hi : e.f i=i') (hnext : c.next i=j) (hnext' : c'.next i'=j')
    (x : M ⟶ K.X i) (hx : x ≫ K.d i j=0)
    (hx' : extensionDegreeLift e K i i' hi x ≫ (K.extend e).d i' j'=0) :
    ((K.extend e).liftCycles (extensionDegreeLift e K i i' hi x) j' hnext' hx' ≫
        (K.extend e).homologyπ i') ≫ (K.extendHomologyIso e hi).hom =
      K.liftCycles x j hnext hx ≫ K.homologyπ i := by
  have he : extensionDegreeLift e K i i' hi x ≫ (𝟙 _ : K.extend e ⟶ K.extend e).f i' ≫
      (K.extendXIso e hi).hom = x := by
    simp only [extensionDegreeLift, HomologicalComplex.id_f, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := extendCycleClass_comparison e (K.extend e) K (𝟙 _) i j i' j' hi hnext hnext'
    (extensionDegreeLift e K i i' hi x) hx' x hx he
  simpa only [HomologicalComplex.homologyMap_id, Category.id_comp, Category.comp_id] using h

end Sharpness
