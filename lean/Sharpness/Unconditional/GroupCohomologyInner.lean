import Sharpness.GroupCohomologyPull

/-! Inner automorphisms act trivially on native group cohomology with
trivial coefficients. The proof uses an explicit endomorphism of the
projective bar resolution and uniqueness of lifts up to chain homotopy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Finsupp
open scoped BigOperators
variable {R G A : Type u} [CommRing R] [Group G]
    [AddCommGroup A] [Module R A]

/-- The equivariant bar map associated to conjugation by `g`, corrected
by left multiplication by `g⁻¹` on its free generators. -/
def innerBarComponent (g : G) (n : ℕ) :
    Rep.free R G (Fin n → G) ⟶ Rep.free R G (Fin n → G) :=
  Rep.freeLift R G _ fun x =>
    single ((MulAut.conj g) ∘ x) (single g⁻¹ 1)

@[simp]
theorem innerBarComponent_single (g : G) (n : ℕ)
    (x : Fin n → G) (h : G) (r : R) :
    (innerBarComponent (R := R) g n).hom (single x (single h r)) =
      single ((MulAut.conj g) ∘ x) (single (h * g⁻¹) r) := by
  simp [innerBarComponent, Rep.freeLift, Representation.freeLift_single_single,
    smul_single, smul_eq_mul]

theorem innerBarComponent_comm (g : G) (n : ℕ) :
    innerBarComponent (R := R) g (n + 1) ≫ Rep.barComplex.d R G n =
      Rep.barComplex.d R G n ≫ innerBarComponent g n := by
  apply Rep.free_ext
  intro x
  simp [Rep.barComplex.d, innerBarComponent, Rep.freeLift,
    Representation.freeLift_single_single, map_add, map_sum,
    MulAut.conj_apply, mul_assoc]
  apply congrArg₂ (· + ·)
  · congr 1
    funext i
    simp [Function.comp_apply, MulAut.conj_apply, mul_assoc]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [← Fin.comp_contractNth (· * ·) (· * ·) (map_mul (MulAut.conj g))]

/-- The corrected conjugation maps form an actual chain endomorphism. -/
def innerBarChain (g : G) : Rep.barComplex R G ⟶ Rep.barComplex R G where
  f n := innerBarComponent g n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simpa only [Rep.barComplex, ChainComplex.of_d] using innerBarComponent_comm (R := R) g j

theorem trivialHom_single {α : Type u}
    (φ : Rep.free R G α ⟶ Rep.trivial R G A) (x : α) (g : G) :
    φ.hom (single x (single g 1)) = φ.hom (single x (single 1 1)) := by
  simpa using Rep.hom_comm_apply φ g (single x (single 1 1))

theorem innerBarChain_augmentation (g : G) :
    innerBarChain (R := R) g ≫ (Rep.barResolution R G).π =
      (Rep.barResolution R G).π := by
  apply HomologicalComplex.to_single_hom_ext
  change innerBarComponent g 0 ≫ (Rep.barResolution R G).π.f 0 =
    (Rep.barResolution R G).π.f 0
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution R G).π.f 0).hom
      ((innerBarComponent g 0).hom (single x (single 1 1))) =
    ((Rep.barResolution R G).π.f 0).hom (single x (single 1 1))
  rw [innerBarComponent_single, one_mul]
  have hx : (MulAut.conj g) ∘ x = x := Subsingleton.elim _ _
  rw [hx]
  exact trivialHom_single ((Rep.barResolution R G).π.f 0) x g⁻¹

/-- Both chain maps lift the identity on the trivial representation. -/
def innerBarHomotopy (g : G) :
    Homotopy (innerBarChain (R := R) g) (𝟙 (Rep.barComplex R G)) :=
  ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial R G R))
    (P := Rep.barResolution R G) (Q := Rep.barResolution R G) _ _
    (by
      change innerBarChain (R := R) g ≫ (Rep.barResolution R G).π =
        (Rep.barResolution R G).π ≫ (ChainComplex.single₀ (Rep R G)).map (𝟙 _)
      rw [(ChainComplex.single₀ (Rep R G)).map_id]
      simpa only [Category.comp_id] using innerBarChain_augmentation (R := R) g)
    (by
      change 𝟙 (Rep.barComplex R G) ≫ (Rep.barResolution R G).π =
        (Rep.barResolution R G).π ≫ (ChainComplex.single₀ (Rep R G)).map (𝟙 _)
      rw [(ChainComplex.single₀ (Rep R G)).map_id]
      simp only [Category.id_comp, Category.comp_id])

/-- Precomposition on the actual Hom complex induced by the bar map. -/
def innerBarHomMap (g : G) :
    (Rep.barComplex R G).linearYonedaObj R (Rep.trivial R G A) ⟶
      (Rep.barComplex R G).linearYonedaObj R (Rep.trivial R G A) :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R (Rep R G)).obj (Rep.trivial R G A)).rightOp.mapHomologicalComplex _).map
      (innerBarChain g)).op

def innerBarHomMapHomotopy (g : G) :
    Homotopy (innerBarHomMap (R := R) (A := A) g) (𝟙 _) := by
  have h := (((linearYoneda R (Rep R G)).obj (Rep.trivial R G A)).rightOp.mapHomotopy
    (innerBarHomotopy (R := R) g)).unop
  refine h.trans (Homotopy.ofEq ?_)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Category.id_comp x

theorem inner_cochain_comparison (g : G) :
    cochainPull (R := R) (A := A) (MulAut.conj g).toMonoidHom ≫
        (groupCohomology.inhomogeneousCochainsIso (Rep.trivial R G A)).hom =
      (groupCohomology.inhomogeneousCochainsIso (Rep.trivial R G A)).hom ≫
        innerBarHomMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Rep.free_ext
  intro y
  change (Rep.freeLift R G (Rep.trivial R G A)
      (fun z => x ((MulAut.conj g) ∘ z))).hom (single y (single 1 1)) =
    (Rep.freeLift R G (Rep.trivial R G A) x).hom
      ((innerBarComponent g n).hom (single y (single 1 1)))
  simp [Rep.freeLift, innerBarComponent, Representation.freeLift_single_single]

/-- Inner automorphisms induce the identity on ordinary group cohomology
with arbitrary trivial coefficients, in every degree. -/
theorem pull_inner (g : G) (n : ℕ) :
    pull (R := R) (A := A) (MulAut.conj g).toMonoidHom n = 𝟙 _ := by
  let e := groupCohomology.inhomogeneousCochainsIso (Rep.trivial R G A)
  apply (cancel_mono (HomologicalComplex.homologyMap e.hom n)).mp
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (inner_cochain_comparison (R := R) (A := A) g)
  have hi := (innerBarHomMapHomotopy (R := R) (A := A) g).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_id] at hi
  simpa only [pull, e, HomologicalComplex.homologyMap_comp, hi, Category.comp_id,
    Category.id_comp] using h

theorem pullLinear_inner (g : G) (n : ℕ) :
    pullLinear (R := R) (A := A) (MulAut.conj g).toMonoidHom n = LinearMap.id :=
  congrArg (fun f : value R G A n ⟶ value R G A n => f.hom) (pull_inner g n)

end Sharpness.OrdinaryCohomology
