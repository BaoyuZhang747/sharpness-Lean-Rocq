import Sharpness.Unconditional.Alperin

/-! Literal finite words of restrictions of centric fusion automorphisms.
The evaluation is an actual group isomorphism, before passage to any orbit category. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- One allowed automorphism of an actual centric subgroup. -/
structure CentricAutomorphism where
  subgroup : Subgroup S
  centric : F.IsCentric subgroup
  automorphism : MulAut subgroup
  allowed : F.IsHom automorphism.toMonoidHom

variable {F}
/-- A restriction onto its precise image subgroup. -/
structure CentricAutomorphism.Restriction (a : F.CentricAutomorphism)
    (P Q : Subgroup S) where
  source_le : P ≤ a.subgroup
  target_le : Q ≤ a.subgroup
  map : P ≃* Q
  apply_eq : ∀ x : P, (map x).val =
    (a.automorphism ⟨x.val, source_le x.property⟩).val

theorem CentricAutomorphism.Restriction.image_eq {a : F.CentricAutomorphism}
    {P Q : Subgroup S} (r : a.Restriction P Q) :
    (fun x : P => (a.automorphism ⟨x.val, r.source_le x.property⟩).val) '' Set.univ =
      (Q : Set S) := by
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    dsimp only
    rw [← r.apply_eq x]
    exact (r.map x).property
  · intro hy
    refine ⟨r.map.symm ⟨y, hy⟩, Set.mem_univ _, ?_⟩
    dsimp only
    rw [← r.apply_eq]
    exact congrArg Subtype.val (r.map.apply_symm_apply ⟨y, hy⟩)

/-- The stored restriction is an allowed fusion isomorphism. -/
theorem CentricAutomorphism.Restriction.allowed {a : F.CentricAutomorphism}
    {P Q : Subgroup S} (r : a.Restriction P Q) : F.IsHom r.map.toMonoidHom := by
  let h : (⟨P⟩ : F.Object) ⟶ ⟨a.subgroup⟩ :=
    F.inclusion r.source_le ≫ (F.isoOfMulEquiv a.automorphism a.allowed).hom
  apply F.codomain_restrict_mem h.val h.property r.target_le r.map.toMonoidHom
  ext x
  exact r.apply_eq x

variable (F)
/-- A dependent finite path indexed by the literal list of centric automorphisms used. -/
inductive CentricFactorization :
    (P Q : Subgroup S) → List F.CentricAutomorphism → Type u
  | nil (P : Subgroup S) : CentricFactorization P P []
  | cons {P Q R : Subgroup S} {l : List F.CentricAutomorphism}
      (a : F.CentricAutomorphism) (step : a.Restriction P Q)
      (tail : CentricFactorization Q R l) : CentricFactorization P R (a :: l)

namespace CentricFactorization
variable {F}

/-- The actual composite of the restricted automorphisms. -/
def comp {P Q : Subgroup S} {l : List F.CentricAutomorphism}
    (w : F.CentricFactorization P Q l) : P ≃* Q :=
  match w with
  | .nil P => MulEquiv.refl P
  | .cons _ step tail => step.map.trans tail.comp

@[simp] theorem comp_nil (P : Subgroup S) :
    (CentricFactorization.nil (F := F) P).comp = MulEquiv.refl P := rfl

/-- Every finite word evaluates to an allowed fusion isomorphism. -/
theorem comp_allowed {P Q : Subgroup S} {l : List F.CentricAutomorphism}
    (w : F.CentricFactorization P Q l) : F.IsHom w.comp.toMonoidHom := by
  induction w with
  | nil P => exact F.id_mem P
  | cons a step tail ih => exact F.comp_mem _ _ step.allowed ih

/-- In particular the identity has a witness of length zero. -/
theorem identity_length_zero (P : Subgroup S) :
    ∃ l : List F.CentricAutomorphism, l.length = 0 ∧
      ∃ w : F.CentricFactorization P P l, w.comp = MulEquiv.refl P :=
  ⟨[], rfl, .nil P, rfl⟩

def append {P Q R : Subgroup S} {l m : List F.CentricAutomorphism}
    (w : F.CentricFactorization P Q l) (v : F.CentricFactorization Q R m) :
    F.CentricFactorization P R (l ++ m) :=
  match w with
  | .nil _ => v
  | .cons a step tail => .cons a step (tail.append v)

theorem comp_append {P Q R : Subgroup S} {l m : List F.CentricAutomorphism}
    (w : F.CentricFactorization P Q l) (v : F.CentricFactorization Q R m) :
    (w.append v).comp = w.comp.trans v.comp := by
  induction w with
  | nil => rfl
  | cons a step tail ih =>
    change step.map.trans (tail.append v).comp = _
    rw [ih]
    rfl

end CentricFactorization

def HasCentricFactorization {P Q : Subgroup S} (e : P ≃* Q) : Prop :=
  ∃ l : List F.CentricAutomorphism, ∃ w : F.CentricFactorization P Q l, w.comp = e

theorem HasCentricFactorization.trans {P Q R : Subgroup S} {e : P ≃* Q} {g : Q ≃* R}
    (he : F.HasCentricFactorization e) (hg : F.HasCentricFactorization g) :
    F.HasCentricFactorization (e.trans g) := by
  obtain ⟨l, w, hw⟩ := he
  obtain ⟨m, v, hv⟩ := hg
  exact ⟨l ++ m, w.append v, by rw [CentricFactorization.comp_append, hw, hv]⟩

/-- Internal induction predicate: every isomorphic restriction has such a finite word. -/
def StronglyCentricFactorizable {P Q : Subgroup S} (e : P ≃* Q) : Prop :=
  ∀ {A B : Subgroup S} (hAP : A ≤ P) (_hBQ : B ≤ Q) (d : A ≃* B),
    (∀ x : A, (d x).val = (e ⟨x.val, hAP x.property⟩).val) →
    F.HasCentricFactorization d

theorem stronglyCentricFactorizable_restrict {P Q A B : Subgroup S} {e : P ≃* Q}
    (he : F.StronglyCentricFactorizable e) (hAP : A ≤ P) (hBQ : B ≤ Q)
    (d : A ≃* B) (hd : ∀ x : A, (d x).val = (e ⟨x.val, hAP x.property⟩).val) :
    F.StronglyCentricFactorizable d := by
  intro C D hCA hDB k hk
  apply he (hCA.trans hAP) (hDB.trans hBQ) k
  intro x
  exact (hk x).trans (hd ⟨x.val, hCA x.property⟩)

theorem stronglyCentricFactorizable_centric_aut {P : Subgroup S}
    (hP : F.IsCentric P) (a : MulAut P) (ha : F.IsHom a.toMonoidHom) :
    F.StronglyCentricFactorizable a := by
  intro A B hAP hBP d hd
  let generator : F.CentricAutomorphism := ⟨P, hP, a, ha⟩
  let step : generator.Restriction A B := ⟨hAP, hBP, d, hd⟩
  exact ⟨[generator], .cons generator step (.nil B), rfl⟩

theorem stronglyCentricFactorizable_trans [Finite S] {P Q R : Subgroup S} {e : P ≃* Q}
    {g : Q ≃* R} (he : F.IsHom e.toMonoidHom)
    (hegen : F.StronglyCentricFactorizable e) (hggen : F.StronglyCentricFactorizable g) :
    F.StronglyCentricFactorizable (e.trans g) := by
  intro A B hAP hBR d hd
  let f₀ : (⟨A⟩ : F.Object) ⟶ ⟨Q⟩ :=
    F.inclusion hAP ≫ (F.isoOfMulEquiv e he).hom
  let i := F.imageIso f₀
  let e₀ := F.alperinMulEquivOfIso i
  let l := e₀.symm.trans d
  have hfirst : F.HasCentricFactorization e₀ :=
    hegen hAP (F.image_le f₀) e₀ (fun _ => rfl)
  have hlast : F.HasCentricFactorization l := by
    apply hggen (F.image_le f₀) hBR l
    intro x
    have heq : e ⟨(e₀.symm x).val, hAP (e₀.symm x).property⟩ =
        ⟨x.val, F.image_le f₀ x.property⟩ := by
      apply Subtype.ext
      exact congrArg (fun z : F.imageSubgroup f₀ => z.val) (e₀.apply_symm_apply x)
    change (d (e₀.symm x)).val = _
    rw [hd]
    change (g (e _)).val = _
    rw [heq]
  have h := HasCentricFactorization.trans F hfirst hlast
  have hcomp : e₀.trans l = d := by
    ext x
    simp [l]
  rwa [hcomp] at h

end Sharpness.FusionSystem
