(** The actual diagonal and finite-total complexes as natural chain diagrams. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules BarFreeModule.
From DiazParkV16b Require Import ChainComplex ModelwiseChainDiagram SimplicialSet SimplicialChainsMaps
  BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyChain
  BisimplicialAlexanderWhitneyNaturality BisimplicialAlexanderWhitneyZero
  FirstQuadrantChainTotal FirstQuadrantChainTotalMaps.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPModelwiseChainDiagram DPSimplicialChainMaps
  DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyChain DPAlexanderWhitneyNaturality
  DPAlexanderWhitneyZero DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps.
Local Open Scope ring_scope.

Module DPBisimplicialChainDiagrams.
Section Diagrams.
Variable R : pzRingType.

Definition bisimplex_degree (p q : nat) : module_diagram R bisimplicial_category.
Proof.
refine (@Build_functor bisimplicial_category (module_category R)
  (fun X => bi_term R X p q)
  (fun X Y a => module_hom_of_linear (free_map R (bisimplex_component a p q))) _ _).
- move=> X; apply module_hom_ext => x; exact: free_map_identity.
- move=> X Y Z a b; apply module_hom_ext => x; exact: free_map_composition.
Defined.

Definition diagonal_degree n := bisimplex_degree n n.

Definition total_degree (n : nat) : module_diagram R bisimplicial_category.
Proof.
refine (@Build_functor bisimplicial_category (module_category R)
  (fun X => chain_term (total_chains R X) n)
  (fun X Y a => module_hom_of_linear (chain_map_at (total_chains_map R a) n)) _ _).
- move=> X; apply module_hom_ext => x.
  apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
    apply functional_extensionality_dep => h.
  exact: free_map_identity.
- move=> X Y Z a b; apply module_hom_ext => x.
  apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
    apply functional_extensionality_dep => h.
  exact: free_map_composition.
Defined.

Definition diagonal_differential n : nat_trans (diagonal_degree n.+1) (diagonal_degree n).
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (diagonal_degree n.+1) (diagonal_degree n)
  (fun X => module_hom_of_linear (chain_d (diagonal_chains R X) n)) _).
move=> X Y a; apply module_hom_ext => x.
exact (@chain_map_commutes R _ _ (diagonal_chains_map R a) n x).
Defined.

Definition total_differential n : nat_trans (total_degree n.+1) (total_degree n).
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (total_degree n.+1) (total_degree n)
  (fun X => module_hom_of_linear (chain_d (total_chains R X) n)) _).
move=> X Y a; apply module_hom_ext => x.
exact (@chain_map_commutes R _ _ (total_chains_map R a) n x).
Defined.

Definition diagonal_diagram : chain_diagram R bisimplicial_category :=
  @ChainDiagram R bisimplicial_category diagonal_degree diagonal_differential
    (fun n X => @chain_d2 R (diagonal_chains R X) n).
Definition total_diagram : chain_diagram R bisimplicial_category :=
  @ChainDiagram R bisimplicial_category total_degree total_differential
    (fun n X => @chain_d2 R (total_chains R X) n).

Definition alexander_whitney_degree n : nat_trans (diagonal_degree n) (total_degree n).
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (diagonal_degree n) (total_degree n)
  (fun X => module_hom_of_linear (chain_map_at (alexander_whitney R X) n)) _).
move=> X Y a; apply module_hom_ext => x; symmetry; exact: alexander_whitney_natural.
Defined.
Definition alexander_whitney_diagram : chain_diagram_map diagonal_diagram total_diagram :=
  @ChainDiagramMap R bisimplicial_category diagonal_diagram total_diagram alexander_whitney_degree
    (fun n X => @chain_map_commutes R _ _ (alexander_whitney R X) n).

Definition alexander_whitney_zero_inverse : nat_trans (total_degree 0%N) (diagonal_degree 0%N).
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (total_degree 0%N) (diagonal_degree 0%N)
  (fun X => module_hom_of_linear (@aw_zero_inverse R X)) _).
move=> X Y a; apply module_hom_ext => x; reflexivity.
Defined.

Lemma alexander_whitney_zero_left : nat_comp (alexander_whitney_degree 0%N) alexander_whitney_zero_inverse = nat_id (diagonal_degree 0%N).
Proof. apply nat_trans_ext => X; apply module_hom_ext => x; exact: aw_zero_left. Qed.
Lemma alexander_whitney_zero_right : nat_comp alexander_whitney_zero_inverse (alexander_whitney_degree 0%N) = nat_id (total_degree 0%N).
Proof. apply nat_trans_ext => X; apply module_hom_ext => x; exact: aw_zero_right. Qed.

Definition alexander_whitney_zero_natural_iso :
  @isomorphism (functor_category bisimplicial_category (module_category R)) (diagonal_degree 0%N) (total_degree 0%N) :=
  @Build_isomorphism (functor_category bisimplicial_category (module_category R))
    (diagonal_degree 0%N) (total_degree 0%N) (alexander_whitney_degree 0%N) alexander_whitney_zero_inverse
    alexander_whitney_zero_left alexander_whitney_zero_right.

Lemma diagonal_evaluation_d (X : bisimplicial_set) n x :
  chain_d (evaluated_chain diagonal_diagram X) n x = chain_d (diagonal_chains R X) n x.
Proof. reflexivity. Qed.
Lemma total_evaluation_d (X : bisimplicial_set) n x :
  chain_d (evaluated_chain total_diagram X) n x = chain_d (total_chains R X) n x.
Proof. reflexivity. Qed.
Lemma alexander_whitney_evaluation (X : bisimplicial_set) n x :
  chain_map_at (evaluated_diagram_map alexander_whitney_diagram X) n x =
  chain_map_at (alexander_whitney R X) n x.
Proof. reflexivity. Qed.
End Diagrams.
End DPBisimplicialChainDiagrams.
