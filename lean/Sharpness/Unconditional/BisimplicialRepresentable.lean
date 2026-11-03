import Sharpness.Unconditional.BisimplicialAlexanderWhitneyNaturality

/-! Actual representable bisimplicial sets and their universal generators.
These are the models for a relative acyclic-models argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite

/-- External product: the two simplicial coordinates vary independently. -/
def bisimplicialExternalProduct (P Q : SSet.{u}) : SimplicialObject SSet.{u} where
  obj a :=
    { obj b := P.obj a × Q.obj b
      map f := ↾fun z => (z.1, Q.map f z.2)
      map_id a := by
        apply ConcreteCategory.hom_ext
        intro z
        change (z.1, Q.map (𝟙 a) z.2) = z
        rw [Q.map_id]
        rfl
      map_comp f g := by
        apply ConcreteCategory.hom_ext
        intro z
        change (z.1, Q.map (f ≫ g) z.2) = (z.1, Q.map g (Q.map f z.2))
        rw [Q.map_comp]
        rfl }
  map f :=
    { app b := ↾fun z => (P.map f z.1, z.2)
      naturality {_ _} g := by
        apply ConcreteCategory.hom_ext
        intro z
        rfl }
  map_id a := by
    apply NatTrans.ext
    funext b
    apply ConcreteCategory.hom_ext
    intro z
    change (P.map (𝟙 a) z.1, z.2) = z
    rw [P.map_id]
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext b
    apply ConcreteCategory.hom_ext
    intro z
    change (P.map (f ≫ g) z.1, z.2) = (P.map g (P.map f z.1), z.2)
    rw [P.map_comp]
    rfl

/-- The bisimplicial representable with universal bidegree `(p,q)`. -/
def bisimplicialRepresentable (p q : ℕ) : SimplicialObject SSet.{u} :=
  bisimplicialExternalProduct Δ[p] Δ[q]

def bisimplicialRepresentableGenerator (p q : ℕ) :
    ((bisimplicialRepresentable.{u} p q).obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋p⦌), SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q⦌))

theorem bisimplicialSimplexPull_naturality {X Y : SimplicialObject SSet.{u}} (φ : X ⟶ Y)
    {p q m n : ℕ} (f : ⦋p⦌ ⟶ ⦋m⦌) (g : ⦋q⦌ ⟶ ⦋n⦌)
    (x : (X.obj (op ⦋m⦌)).obj (op ⦋n⦌)) :
    (φ.app (op ⦋p⦌)).app (op ⦋q⦌) (bisimplicialSimplexPull X f g x) =
      bisimplicialSimplexPull Y f g ((φ.app (op ⦋m⦌)).app (op ⦋n⦌) x) :=
  congrArg (fun z => z x) ((Functor.uncurry.map φ).naturality
    (show (op ⦋m⦌, op ⦋n⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (f.op, g.op)))

/-- The map classified by an actual bisimplex. -/
def bisimplicialRepresentableMap (X : SimplicialObject SSet.{u}) {p q : ℕ}
    (x : (X.obj (op ⦋p⦌)).obj (op ⦋q⦌)) : bisimplicialRepresentable p q ⟶ X where
  app a :=
    { app b := ↾fun z => bisimplicialSimplexPull X
        (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2) x
      naturality {b c} f := by
        ext z
        change bisimplicialSimplexPull X (SSet.stdSimplex.objEquiv z.1)
            (f.unop ≫ SSet.stdSimplex.objEquiv z.2) x =
          (X.obj a).map f (bisimplicialSimplexPull X
            (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2) x)
        have hf := bisimplicialSimplexPull_id_left X (m := a.unop.len) f.unop
        change bisimplicialSimplexPull X (𝟙 ⦋a.unop.len⦌) f.unop = (X.obj a).map f at hf
        rw [← hf,
          bisimplicialSimplexPull_comp_apply, Category.id_comp] }
  naturality {a b} f := by
    ext c z
    change bisimplicialSimplexPull X
        (f.unop ≫ SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2) x =
      (X.map f).app c (bisimplicialSimplexPull X
        (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2) x)
    have hf := bisimplicialSimplexPull_id_right X (n := c.unop.len) f.unop
    change bisimplicialSimplexPull X f.unop (𝟙 ⦋c.unop.len⦌) = (X.map f).app c at hf
    rw [← hf,
      bisimplicialSimplexPull_comp_apply, Category.id_comp]

theorem bisimplicialRepresentableMap_generator (X : SimplicialObject SSet.{u}) {p q : ℕ}
    (x : (X.obj (op ⦋p⦌)).obj (op ⦋q⦌)) :
    ((bisimplicialRepresentableMap X x).app (op ⦋p⦌)).app (op ⦋q⦌)
        (bisimplicialRepresentableGenerator p q) = x := by
  change bisimplicialSimplexPull X (𝟙 ⦋p⦌) (𝟙 ⦋q⦌) x = x
  rw [bisimplicialSimplexPull_id_left]
  simp

theorem bisimplicialRepresentable_generator_pull (p q a b : ℕ)
    (z : ((bisimplicialRepresentable.{u} p q).obj (op ⦋a⦌)).obj (op ⦋b⦌)) :
    bisimplicialSimplexPull (bisimplicialRepresentable p q)
        (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2)
        (bisimplicialRepresentableGenerator p q) = z := by
  rcases z with ⟨⟨f⟩, ⟨g⟩⟩
  apply Prod.ext
  · change ULift.up (f ≫ 𝟙 _) = ULift.up f
    rw [Category.comp_id]
  · change ULift.up (g ≫ 𝟙 _) = ULift.up g
    rw [Category.comp_id]

/-- All components of a map out of a model are determined by one generator. -/
theorem bisimplicialRepresentable_hom_ext {X : SimplicialObject SSet.{u}} {p q : ℕ}
    {f g : bisimplicialRepresentable p q ⟶ X}
    (h : (f.app (op ⦋p⦌)).app (op ⦋q⦌) (bisimplicialRepresentableGenerator p q) =
      (g.app (op ⦋p⦌)).app (op ⦋q⦌) (bisimplicialRepresentableGenerator p q)) : f = g := by
  ext a b z
  have hf := bisimplicialSimplexPull_naturality f
    (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2)
    (bisimplicialRepresentableGenerator p q)
  have hg := bisimplicialSimplexPull_naturality g
    (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2)
    (bisimplicialRepresentableGenerator p q)
  rw [bisimplicialRepresentable_generator_pull] at hf hg
  exact hf.trans ((congrArg (bisimplicialSimplexPull X
    (SSet.stdSimplex.objEquiv z.1) (SSet.stdSimplex.objEquiv z.2)) h).trans hg.symm)

def bisimplicialRepresentableEquiv (X : SimplicialObject SSet.{u}) (p q : ℕ) :
    (bisimplicialRepresentable p q ⟶ X) ≃ (X.obj (op ⦋p⦌)).obj (op ⦋q⦌) where
  toFun f := (f.app (op ⦋p⦌)).app (op ⦋q⦌) (bisimplicialRepresentableGenerator p q)
  invFun := bisimplicialRepresentableMap X
  left_inv f := bisimplicialRepresentable_hom_ext (bisimplicialRepresentableMap_generator X _)
  right_inv := bisimplicialRepresentableMap_generator X

end Sharpness
