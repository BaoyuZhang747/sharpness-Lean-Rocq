(** Actual singular simplices and chains of a subtype, identified with their ambient image. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology initial_topology.
From DiazPark Require Import Category CategoryExtensionality BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSubcomplex
  SingularSet SingularCohomology SimplicialChains SimplicialChainsMaps
  ChainComplex FreeModuleEmbeddings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPSimplexCategory DPSimplicialTypes
  DPSimplicialSubcomplex DPSingularSet DPSingularCohomology DPSimplicialChains
  DPSimplicialChainMaps DPChainComplex DPFreeModuleEmbeddings.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularChainExcisionSubspaces.
Section Subspaces.
Variable Real : realType.
Variable X : topologicalType.
Variable A : set X.

Definition subset_space : topologicalType := [the topologicalType of set_type A].

Definition subset_inclusion : hom topological_category subset_space X.
Proof.
apply: (@continuous_map subset_space X set_val).
exact: initial_continuous.
Defined.

Definition landing_subcomplex : subcomplex (singular_set Real X).
Proof.
refine (@Subcomplex (singular_set Real X) (fun n s => forall t, A (s t)) _).
move=> n m f s hs t; exact: hs.
Defined.

Definition lift_landing_simplex n
    (s : DPSimplicialSet.simplex (singular_set Real X) n)
    (hs : member landing_subcomplex n s) :
    DPSimplicialSet.simplex (singular_set Real subset_space) n.
Proof.
pose f := fun t : DPTopologicalSimplex.simplex Real n =>
  (exist _ (s t) (mem_set (hs t)) : set_type A).
apply: (@continuous_map (DPTopologicalSimplex.simplex_space Real n) subset_space f).
apply: (@continuous_comp_initial [the choiceType of set_type A]
  (DPTopologicalSimplex.simplex_space Real n) X set_val f).
change (continuous s); exact: cts_fun.
Defined.

Lemma lift_landing_simplex_at n
    (s : DPSimplicialSet.simplex (singular_set Real X) n)
    (hs : member landing_subcomplex n s) t :
  subset_inclusion (lift_landing_simplex hs t) = s t.
Proof. reflexivity. Qed.

Definition subspace_to_landing :
    DPSimplicialSet.simplicial_map (singular_set Real subset_space)
      (subcomplex_set landing_subcomplex).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (singular_set Real subset_space) (subcomplex_set landing_subcomplex)
  (fun n s => exist (fun z : DPSimplicialSet.simplex (singular_set Real X) n =>
      member landing_subcomplex n z) (continuous_compose s subset_inclusion)
    (fun t => set_valP (s t))) _).
move=> n m f; apply type_morphism_ext => s.
apply subcomplex_simplex_ext; apply topological_hom_ext => t; reflexivity.
Defined.

Definition landing_to_subspace :
    DPSimplicialSet.simplicial_map (subcomplex_set landing_subcomplex)
      (singular_set Real subset_space).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (subcomplex_set landing_subcomplex) (singular_set Real subset_space)
  (fun n s => lift_landing_simplex (proj2_sig s)) _).
move=> n m f; apply type_morphism_ext => s.
apply topological_hom_ext => t; apply val_inj; reflexivity.
Defined.

Lemma landing_subspaceK n (s : DPSimplicialSet.simplex (singular_set Real subset_space) n) :
  component landing_to_subspace n (component subspace_to_landing n s) = s.
Proof. apply topological_hom_ext => t; apply val_inj; reflexivity. Qed.

Lemma subspace_landingK n (s : subcomplex_simplex landing_subcomplex n) :
  component subspace_to_landing n (component landing_to_subspace n s) = s.
Proof. apply subcomplex_simplex_ext; apply topological_hom_ext => t; reflexivity. Qed.

Lemma subspace_to_landing_inclusion :
  nat_comp subspace_to_landing (subcomplex_inclusion landing_subcomplex) =
    singular_map Real subset_inclusion.
Proof. apply nat_trans_ext => n; reflexivity. Qed.

Lemma subspace_singular_inclusion_injective n :
  injective (component (singular_map Real subset_inclusion) n).
Proof.
move=> s t h; apply topological_hom_ext => x; apply val_inj.
exact (congr1 (fun f : DPSimplicialSet.simplex (singular_set Real X) n => f x) h).
Qed.

Lemma subspace_singular_image n (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  (exists t, component (singular_map Real subset_inclusion) n t = s) <->
    member landing_subcomplex n s.
Proof.
split.
- move=> [t <-] x; exact: set_valP (t x).
- move=> hs; exists (lift_landing_simplex hs).
  apply topological_hom_ext => x; reflexivity.
Qed.

Variable R : pzRingType.

Definition subspace_chain_inclusion := singular_chain_map Real R subset_inclusion.
Definition landing_chains := chains R (subcomplex_set landing_subcomplex).
Definition landing_chain_inclusion := chain_map_of R (subcomplex_inclusion landing_subcomplex).
Definition subspace_to_landing_chains := chain_map_of R subspace_to_landing.
Definition landing_to_subspace_chains := chain_map_of R landing_to_subspace.

Lemma subspace_chain_inclusion_injective n :
  injective (chain_map_at subspace_chain_inclusion n).
Proof. apply free_map_injective; exact: subspace_singular_inclusion_injective. Qed.

Lemma landing_subspace_chainsK n (a : chain_term (singular_chains Real R subset_space) n) :
  chain_map_at landing_to_subspace_chains n (chain_map_at subspace_to_landing_chains n a) = a.
Proof.
apply (free_lift_ext
  (g := (chain_map_at landing_to_subspace_chains n \o chain_map_at subspace_to_landing_chains n : {linear _ -> _}))
  (h := (idfun : {linear chain_term (singular_chains Real R subset_space) n -> _}))).
move=> s.
change (map_at R landing_to_subspace n (map_at R subspace_to_landing n (free_basis R s)) = free_basis R s).
by rewrite !map_at_basis landing_subspaceK.
Qed.

Lemma subspace_landing_chainsK n (a : chain_term landing_chains n) :
  chain_map_at subspace_to_landing_chains n (chain_map_at landing_to_subspace_chains n a) = a.
Proof.
apply (free_lift_ext
  (g := (chain_map_at subspace_to_landing_chains n \o chain_map_at landing_to_subspace_chains n : {linear _ -> _}))
  (h := (idfun : {linear chain_term landing_chains n -> _}))).
move=> s.
change (map_at R subspace_to_landing n (map_at R landing_to_subspace n (free_basis R s)) = free_basis R s).
by rewrite !map_at_basis subspace_landingK.
Qed.

Lemma subspace_to_landing_chain_inclusion n
    (a : chain_term (singular_chains Real R subset_space) n) :
  chain_map_at landing_chain_inclusion n (chain_map_at subspace_to_landing_chains n a) =
    chain_map_at subspace_chain_inclusion n a.
Proof.
change (map_at R (subcomplex_inclusion landing_subcomplex) n (map_at R subspace_to_landing n a) =
  map_at R (singular_map Real subset_inclusion) n a).
by rewrite -map_composition subspace_to_landing_inclusion.
Qed.

Lemma landing_to_subspace_chain_inclusion n (a : chain_term landing_chains n) :
  chain_map_at subspace_chain_inclusion n (chain_map_at landing_to_subspace_chains n a) =
    chain_map_at landing_chain_inclusion n a.
Proof.
by rewrite -subspace_to_landing_chain_inclusion subspace_landing_chainsK.
Qed.

Theorem subspace_chain_image n (a : chain_term (singular_chains Real R X) n) :
  (exists b, chain_map_at subspace_chain_inclusion n b = a) <->
    exists b, chain_map_at landing_chain_inclusion n b = a.
Proof.
split=> [][b <-].
- exists (chain_map_at subspace_to_landing_chains n b); exact: subspace_to_landing_chain_inclusion.
- exists (chain_map_at landing_to_subspace_chains n b); exact: landing_to_subspace_chain_inclusion.
Qed.

End Subspaces.
End DPSingularChainExcisionSubspaces.
