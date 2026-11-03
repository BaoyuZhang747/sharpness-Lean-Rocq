import Sharpness.Unconditional.NormalizerOrbitExtensionConjugacy
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.FinRange

/-! The actual category of centric acting subgroups and normalized centric
chains. Arrows are centric orbit maps admitting a simultaneous fusion
extension on a selected subchain. Both indexing projections are constructed;
no comma-cofinality assertion is made here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

structure NormalizerOrbitPair where
  centric : F.CentricOrbit
  chain : F.CentricChain
  normalizes : ∀ i, centric.obj.as.subgroup ≤ Subgroup.normalizer (chain.subgroup i : Set S)

namespace NormalizerOrbitPair
variable {F} (A B D : F.NormalizerOrbitPair)

abbrev Hom := {f : A.centric ⟶ B.centric //
  ∃ g : A.centric.obj.as ⟶ B.centric.obj.as,
    F.toOrbit.map g = f.hom ∧ Nonempty (F.NormalizerChainExtension A.chain B.chain g)}

def identity : A.Hom A :=
  ⟨𝟙 A.centric,𝟙 A.centric.obj.as,F.toOrbit.map_id _,
    ⟨NormalizerChainExtension.identity _ _⟩⟩

def composition (f : A.Hom B) (g : B.Hom D) : A.Hom D := by
  refine ⟨f.val ≫ g.val,?_⟩
  obtain ⟨f₀,hf₀,⟨hf⟩⟩ := f.property
  obtain ⟨g₀,hg₀,⟨hg⟩⟩ := g.property
  refine ⟨f₀ ≫ g₀,?_,⟨hf.comp hg⟩⟩
  rw [F.toOrbit.map_comp,hf₀,hg₀]
  rfl

instance : Category (F.NormalizerOrbitPair) where
  Hom A B := A.Hom B
  id A := A.identity
  comp f g := composition _ _ _ f g
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

@[ext] theorem hom_ext {A B : F.NormalizerOrbitPair} (f g : A ⟶ B)
    (h : f.val = g.val) : f = g := Subtype.ext h

def homMk {A B : F.NormalizerOrbitPair}
    (g : A.centric.obj.as ⟶ B.centric.obj.as)
    (a : F.NormalizerChainExtension A.chain B.chain g) : A ⟶ B :=
  ⟨ObjectProperty.homMk (F.toOrbit.map g),g,rfl,⟨a⟩⟩

theorem isSubconjugate {A B : F.NormalizerOrbitPair} (f : A ⟶ B) :
    CentricChain.IsSubconjugate A.chain B.chain := by
  obtain ⟨_,_,⟨a⟩⟩ := f.property
  exact a.isSubconjugate

end NormalizerOrbitPair

def normalizerOrbitPairForget : F.NormalizerOrbitPair ⥤ F.CentricOrbit where
  obj A := A.centric
  map f := f.val

instance normalizerOrbitPairForget_faithful : F.normalizerOrbitPairForget.Faithful where
  map_injective h := Subtype.ext h

def normalizerOrbitPairProjection : F.NormalizerOrbitPair ⥤ F.NormalizerCategory where
  obj A := F.normalizerClass A.chain
  map f := homOfLE (NormalizerOrbitPair.isSubconjugate f)

instance centricChain_finite [Finite S] : Finite F.CentricChain := by
  classical
  letI : Fintype F.CentricSubgroup := Fintype.ofFinite _
  let encode : F.CentricChain → {l : List F.CentricSubgroup // l.Nodup} := fun σ =>
    ⟨List.ofFn σ.entry,List.nodup_ofFn_ofInjective (fun i j h =>
      σ.strict.injective (congrArg Subtype.val h))⟩
  apply Finite.of_injective encode
  intro σ τ h
  have hfn := congrArg Subtype.val h
  have hn := congrArg List.length hfn
  change (List.ofFn σ.entry).length = (List.ofFn τ.entry).length at hn
  simp only [List.length_ofFn] at hn
  have hn' : σ.length = τ.length := Nat.succ.inj hn
  cases σ with
  | mk n e he =>
    cases τ with
    | mk m d hd =>
      change n = m at hn'
      subst m
      change List.ofFn e = List.ofFn d at hfn
      have hed : e = d := List.ofFn_injective hfn
      subst d
      rfl

instance normalizerOrbitPair_finite [Finite S] : Finite F.NormalizerOrbitPair := by
  letI : Finite F.CentricOrbit := Finite.of_injective
    (fun A : F.CentricOrbit => A.obj) (by
      intro A B h
      cases A
      cases B
      cases h
      rfl)
  apply Finite.of_injective (fun A : F.NormalizerOrbitPair => (A.centric,A.chain))
  intro A B h
  cases A
  cases B
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
  cases h₁
  cases h₂
  rfl

instance normalizerOrbitPair_hom_finite [Finite S] (A B : F.NormalizerOrbitPair) :
    Finite (A ⟶ B) := by
  letI : Finite (A.centric ⟶ B.centric) := Finite.of_injective
    (fun f : A.centric ⟶ B.centric => f.hom) (fun _ _ h => InducedCategory.hom_ext h)
  exact inferInstanceAs (Finite (A.Hom B))

end Sharpness.FusionSystem
