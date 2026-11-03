(** Literal inclusions, intersections, and binary-small unions of subspace simplices. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology initial_topology.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import TopologicalCategory SimplexCategoryTypes SimplicialSet
  SimplicialSubcomplex SingularSet SingularSmallChains SingularChainExcisionSubspaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSimplicialTypes DPSimplicialSubcomplex DPSingularSet
  DPSingularSmallChains DPSingularChainExcisionSubspaces.
Local Open Scope classical_set_scope.

Module DPSingularChainExcisionSubspacesLattice.
Section Subsets.
Variable Real : realType.
Variable X : topologicalType.

Definition subset_map (A B : set X) (h : A `<=` B) :
    hom topological_category (subset_space A) (subset_space B).
Proof.
pose f := fun x : set_type A => (exist _ (set_val x) (mem_set (h _ (set_valP x))) : set_type B).
apply: (@continuous_map (subset_space A) (subset_space B) f).
apply: (@continuous_comp_initial [the choiceType of set_type B]
  (subset_space A) X set_val f).
change (continuous (@set_val X A)); exact: initial_continuous.
Defined.

Lemma subset_map_at (A B : set X) (h : A `<=` B) x : set_val (subset_map h x) = set_val x.
Proof. reflexivity. Qed.

Lemma subset_map_inclusion (A B : set X) (h : A `<=` B) :
  compose (subset_map h) (subset_inclusion B) = subset_inclusion A.
Proof. apply topological_hom_ext => x; reflexivity. Qed.

Lemma subset_map_identity (A : set X) (h : A `<=` A) :
  subset_map h = @identity topological_category (subset_space A).
Proof. apply topological_hom_ext => x; apply val_inj; reflexivity. Qed.

Lemma subset_map_compose (A B C : set X) (h : A `<=` B) (k : B `<=` C) (l : A `<=` C) :
  compose (subset_map h) (subset_map k) = subset_map l.
Proof. apply topological_hom_ext => x; apply val_inj; reflexivity. Qed.

Lemma landing_subcomplex_mono (A B : set X) (h : A `<=` B) :
  subcomplex_le (landing_subcomplex Real A) (landing_subcomplex Real B).
Proof. move=> n s hs t; exact: h (hs t). Qed.

Lemma subspace_to_landing_natural (A B : set X) (h : A `<=` B) :
  nat_comp (singular_map Real (subset_map h)) (subspace_to_landing Real B) =
  nat_comp (subspace_to_landing Real A) (subcomplex_map (landing_subcomplex_mono h)).
Proof.
apply nat_trans_ext => n; apply type_morphism_ext => s.
apply subcomplex_simplex_ext; apply topological_hom_ext => t; reflexivity.
Qed.

Lemma landing_intersection (A B : set X) :
  landing_subcomplex Real (A `&` B) =
    subcomplex_intersection (landing_subcomplex Real A) (landing_subcomplex Real B).
Proof.
apply subcomplex_ext => n s; split.
- move=> h; split=> t; [exact: (proj1 (h t)) | exact: (proj2 (h t))].
- move=> [hA hB] t; split; [exact: hA | exact: hB].
Qed.

Definition binary_cover (A B : set X) (b : bool) : set X := if b then A else B.

Lemma binary_small_union (A B : set X) :
  small_subcomplex Real (binary_cover A B) =
    subcomplex_union (landing_subcomplex Real A) (landing_subcomplex Real B).
Proof.
apply subcomplex_ext => n s; split.
- move=> [][|] hs; [left | right]; exact: hs.
- move=> [hs|hs]; [exists true | exists false]; exact: hs.
Qed.

Lemma landing_union_inclusion (A B : set X) :
  subcomplex_le (subcomplex_union (landing_subcomplex Real A) (landing_subcomplex Real B))
    (landing_subcomplex Real (A `|` B)).
Proof. move=> n s [hA|hB] t; [left; exact: hA | right; exact: hB]. Qed.

Lemma binary_cover_open (A B : set X) :
  open A -> open B -> forall b, open (binary_cover A B b).
Proof. by move=> hA hB [|]. Qed.

Lemma binary_cover_covers (A B : set X) :
  (forall x, A x \/ B x) -> forall x, exists b, binary_cover A B b x.
Proof. move=> h x; case: (h x) => hx; [exists true | exists false]; exact: hx. Qed.

End Subsets.
End DPSingularChainExcisionSubspacesLattice.
