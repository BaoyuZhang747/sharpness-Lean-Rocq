import Sharpness.Unconditional.GroupCohomologyMackeyDecomposition

/-! The inverse of the actual double-coset decomposition and its
right-translation equivariance. This is a representation isomorphism, not
yet a cohomological Mackey identity. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
open CategoryTheory

variable {R : Type u} {G : Type v} {A : Type w} [CommRing R] [Group G]
    [AddCommGroup A] [Module R A] (H K : Subgroup G)

def leftCoordinate (g : G) : H := (exists_coordinates H K g).choose

def rightCoordinate (g : G) : K := (exists_coordinates H K g).choose_spec.choose

theorem coordinates_spec (g : G) :
    g = (leftCoordinate H K g : G) * (DoubleCoset.mk H K g).out *
      rightCoordinate H K g :=
  (exists_coordinates H K g).choose_spec.choose_spec

def assembleValue (v : Components (R := R) (A := A) H K) (g : G) : A :=
  (v (DoubleCoset.mk H K g)).1 (rightCoordinate H K g)

/-- The value obtained from the chosen coordinates equals the value in
any coordinates of the same double coset. -/
theorem assembleValue_coordinates (v : Components (R := R) (A := A) H K)
    (d : DoubleCoset.Quotient (H : Set G) K) (h : H) (k : K) :
    assembleValue H K v ((h : G) * d.out * k) = (v d).1 k := by
  let g : G := (h : G) * d.out * k
  have hd : DoubleCoset.mk H K g = d := by
    calc
      DoubleCoset.mk H K g = DoubleCoset.mk H K d.out :=
        ((DoubleCoset.eq H K d.out g).mpr ⟨h, h.2, k, k.2, rfl⟩).symm
      _ = d := DoubleCoset.out_eq' H K d
  change (v (DoubleCoset.mk H K g)).1 (rightCoordinate H K g) = _
  rw [hd]
  apply component_coordinates_eq H K d.out (v d) (leftCoordinate H K g) h
  have hc := coordinates_spec H K g
  rw [hd] at hc
  exact hc.symm

theorem assembleValue_left (v : Components (R := R) (A := A) H K) (h : H) (g : G) :
    assembleValue H K v ((h : G) * g) = assembleValue H K v g := by
  obtain ⟨h₀, k, hg⟩ := exists_coordinates H K g
  let d := DoubleCoset.mk H K g
  calc
    assembleValue H K v ((h : G) * g) =
        assembleValue H K v (((h * h₀ : H) : G) * d.out * k) := by
      rw [hg]
      simp only [d, Subgroup.coe_mul, mul_assoc]
    _ = (v d).1 k := assembleValue_coordinates H K v d (h * h₀) k
    _ = assembleValue H K v g := by
      conv_rhs => rw [hg]
      exact (assembleValue_coordinates H K v d h₀ k).symm

/-- Assemble an actual H-equivariant function from its double-coset pieces. -/
def assemble : Components (R := R) (A := A) H K →ₗ[R] Source (R := R) (A := A) H where
  toFun v := ⟨assembleValue H K v, assembleValue_left H K v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem assemble_decompose (f : Source (R := R) (A := A) H) :
    assemble H K (decompose H K f) = f := by
  apply Subtype.ext
  funext g
  change f.1 ((DoubleCoset.mk H K g).out * rightCoordinate H K g) = f.1 g
  have hf := f.2 (leftCoordinate H K g)
    ((DoubleCoset.mk H K g).out * rightCoordinate H K g)
  conv_rhs => rw [coordinates_spec H K g]
  simpa [Representation.trivial, mul_assoc] using hf.symm

theorem decompose_assemble (v : Components (R := R) (A := A) H K) :
    decompose H K (assemble H K v) = v := by
  funext d
  apply Subtype.ext
  funext k
  change assembleValue H K v (d.out * k) = (v d).1 k
  simpa using assembleValue_coordinates H K v d 1 k

/-- The actual linear equivalence of coinduction with its double-coset pieces. -/
def linearEquiv : Source (R := R) (A := A) H ≃ₗ[R] Components (R := R) (A := A) H K :=
  { decompose H K with
    invFun := assemble H K
    left_inv := assemble_decompose H K
    right_inv := decompose_assemble H K }

/-- Right translation acts separately on every native coinduced component. -/
def componentProductAction (k : K) :
    Components (R := R) (A := A) H K →ₗ[R] Components (R := R) (A := A) H K :=
  LinearMap.pi fun d =>
    (Representation.coind (intersection H K d.out).subtype
      (Representation.trivial R (intersection H K d.out) A) k).comp (LinearMap.proj d)

def productRepresentation : Representation R K (Components (R := R) (A := A) H K) where
  toFun := componentProductAction H K
  map_one' := by
    ext v d k
    change (v d).1 (k * 1) = (v d).1 k
    rw [mul_one]
  map_mul' k k' := by
    ext v d x
    change (v d).1 (x * (k * k')) = (v d).1 ((x * k) * k')
    rw [mul_assoc]

/-- The linear decomposition intertwines the restricted ambient action
with the product of the actual intersection-coinduced actions. -/
def representationEquiv : Representation.Equiv
    ((Representation.coind H.subtype (Representation.trivial R H A)).comp K.subtype)
      (productRepresentation (R := R) (A := A) H K) :=
  .mk (linearEquiv H K) (fun k => by
    ext f d x
    change f.1 ((d.out * x) * k) = f.1 (d.out * (x * k))
    rw [mul_assoc])

/-- The genuine representation-level Mackey decomposition for trivial
coefficients. For finite G its product has finitely many factors. -/
def coinductionMackeyIso :
    Rep.res K.subtype (Rep.coind H.subtype (Rep.trivial R H A)) ≅
      Rep.of (productRepresentation (R := R) (A := A) H K) :=
  Rep.mkIso (representationEquiv H K)

@[simp] theorem coinductionMackeyIso_hom_apply
    (f : Source (R := R) (A := A) H)
    (d : DoubleCoset.Quotient (H : Set G) K) (k : K) :
    (((coinductionMackeyIso (R := R) (A := A) H K).hom.hom f) d).1 k =
      f.1 (d.out * k) := rfl

end Sharpness.OrdinaryCohomology.MackeyDecomposition
