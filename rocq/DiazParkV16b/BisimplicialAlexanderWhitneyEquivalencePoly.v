(** Unconditional natural inverse and both homotopies for the literal Alexander-Whitney map. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism
  ModelwiseChainDiagram ModelwisePresentation ModelwiseChainMap ModelwiseChainHomotopyPoly
  BisimplicialSet BisimplicialChains BisimplicialRepresentable BisimplicialChainDiagrams
  BisimplicialDegreePresentation BisimplicialTotalPresentation BisimplicialAugmentation
  BisimplicialAlexanderWhitneyChain BisimplicialAlexanderWhitneyZero
  BisimplicialRepresentableDiagonalContraction BisimplicialRepresentableTotalExact
  FirstQuadrantChainTotalProjective.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPModelwiseChainDiagram DPModelwisePresentation DPModelwiseChainMap DPModelwiseChainHomotopyPoly
  DPBisimplicialSet DPBisimplicialChains DPBisimplicialRepresentable DPBisimplicialChainDiagrams
  DPBisimplicialDegreePresentation DPBisimplicialTotalPresentation DPBisimplicialAugmentation
  DPAlexanderWhitneyChain DPAlexanderWhitneyZero DPBisimplicialRepresentableDiagonalContraction
  DPBisimplicialRepresentableTotalExact DPFirstQuadrantChainTotalProjective.
Local Open Scope ring_scope.

Module DPAlexanderWhitneyEquivalencePoly.
Section Equivalence.
Variable R : pzRingType.
Let D := diagonal_diagram R.
Let T := total_diagram R.
Let aw := alexander_whitney_diagram R.
Let a0 := alexander_whitney_zero_inverse R.

Lemma inverse_one (i : 'I_2) : exists y : fobj (diagram_degree D 1%N) (total_model i),
  diagram_apply (diagram_d D 0%N) (total_model i) y =
    diagram_apply a0 (total_model i) (diagram_apply (diagram_d T 0%N) (total_model i)
      (model_generator (total_presentation R 1%N) i)).
Proof.
apply (@representable_diagonal_augmentation_exact (val i) (diagonal_second i) R).
exact (@total_augmentation_boundary R (total_model i) (model_generator (total_presentation R 1%N) i)).
Qed.

Lemma inverse_positive n (i : 'I_n.+3) (x : fobj (diagram_degree D n.+1) (total_model i)) :
  diagram_apply (diagram_d D n) (total_model i) x = 0 ->
  exists y, diagram_apply (diagram_d D n.+1) (total_model i) y = x.
Proof. exact (@representable_diagonal_positive_exact (val i) (diagonal_second i) R n x). Qed.

Definition inverse_diagram : chain_diagram_map T D :=
  @modelwise_chain_map R bisimplicial_category T D (fun n => 'I_n.+1)
    (fun n => @total_model n) (total_presentation R) a0 inverse_one inverse_positive.

Lemma inverse_diagram_zero : diagram_map_degree inverse_diagram 0%N = a0.
Proof. reflexivity. Qed.

Lemma left_zero : diagram_map_degree (diagram_composition aw inverse_diagram) 0%N =
  diagram_map_degree (diagram_identity D) 0%N.
Proof. exact: alexander_whitney_zero_left. Qed.
Lemma right_zero : diagram_map_degree (diagram_composition inverse_diagram aw) 0%N =
  diagram_map_degree (diagram_identity T) 0%N.
Proof. exact: alexander_whitney_zero_right. Qed.

Lemma diagonal_models_positive n (i : unit) (x : fobj (diagram_degree D n.+1) (degree_model n.+1 n.+1 i)) :
  diagram_apply (diagram_d D n) (degree_model n.+1 n.+1 i) x = 0 ->
  exists y, diagram_apply (diagram_d D n.+1) (degree_model n.+1 n.+1 i) y = x.
Proof. exact (@representable_diagonal_positive_exact n.+1 n.+1 R n x). Qed.
Lemma total_models_positive n (i : 'I_n.+2) (x : fobj (diagram_degree T n.+1) (total_model i)) :
  diagram_apply (diagram_d T n) (total_model i) x = 0 ->
  exists y, diagram_apply (diagram_d T n.+1) (total_model i) y = x.
Proof. exact (@representable_total_positive_exact R (val i) (diagonal_second i) n x). Qed.

Definition left_diagram_homotopy : chain_diagram_homotopy (diagram_composition aw inverse_diagram) (diagram_identity D) :=
  @modelwise_chain_homotopy R bisimplicial_category D D (diagram_composition aw inverse_diagram) (diagram_identity D)
    (fun _ => unit) (fun n => degree_model n n) (diagonal_presentation R) left_zero diagonal_models_positive.
Definition right_diagram_homotopy : chain_diagram_homotopy (diagram_composition inverse_diagram aw) (diagram_identity T) :=
  @modelwise_chain_homotopy R bisimplicial_category T T (diagram_composition inverse_diagram aw) (diagram_identity T)
    (fun n => 'I_n.+1) (fun n => @total_model n) (total_presentation R) right_zero total_models_positive.

Definition alexander_whitney_inverse (X : bisimplicial_set) :
  chain_map (total_chains R X) (diagonal_chains R X) :=
  @ChainMap R (total_chains R X) (diagonal_chains R X)
    (fun n => module_hom_to_linear (component (diagram_map_degree inverse_diagram n) X))
    (fun n => diagram_map_d inverse_diagram n X).

Definition alexander_whitney_left_homotopy (X : bisimplicial_set) :
  chain_homotopy (chain_composition (alexander_whitney R X) (alexander_whitney_inverse X))
    (chain_identity (diagonal_chains R X)) :=
  @ChainHomotopy R (diagonal_chains R X) (diagonal_chains R X)
    (chain_composition (alexander_whitney R X) (alexander_whitney_inverse X)) (chain_identity (diagonal_chains R X))
    (fun n => module_hom_to_linear (component (diagram_homotopy_degree left_diagram_homotopy n) X))
    (diagram_homotopy_zero left_diagram_homotopy X)
    (fun n => diagram_homotopy_succ left_diagram_homotopy n X).
Definition alexander_whitney_right_homotopy (X : bisimplicial_set) :
  chain_homotopy (chain_composition (alexander_whitney_inverse X) (alexander_whitney R X))
    (chain_identity (total_chains R X)) :=
  @ChainHomotopy R (total_chains R X) (total_chains R X)
    (chain_composition (alexander_whitney_inverse X) (alexander_whitney R X)) (chain_identity (total_chains R X))
    (fun n => module_hom_to_linear (component (diagram_homotopy_degree right_diagram_homotopy n) X))
    (diagram_homotopy_zero right_diagram_homotopy X)
    (fun n => diagram_homotopy_succ right_diagram_homotopy n X).

Lemma alexander_whitney_homology_left (X : bisimplicial_set) n x :
  homology_map (alexander_whitney_inverse X) n (homology_map (alexander_whitney R X) n x) = x.
Proof.
rewrite -homology_map_composition (homology_map_homotopy (alexander_whitney_left_homotopy X)).
exact: homology_map_identity.
Qed.
Lemma alexander_whitney_homology_right (X : bisimplicial_set) n x :
  homology_map (alexander_whitney R X) n (homology_map (alexander_whitney_inverse X) n x) = x.
Proof.
rewrite -homology_map_composition (homology_map_homotopy (alexander_whitney_right_homotopy X)).
exact: homology_map_identity.
Qed.

Definition alexander_whitney_homology_iso (X : bisimplicial_set) n :
  @isomorphism (module_category R) (homology (diagonal_chains R X) n) (homology (total_chains R X) n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (homology_map (alexander_whitney R X) n))
  (module_hom_of_linear (homology_map (alexander_whitney_inverse X) n)) _ _).
- apply module_hom_ext => x; exact: alexander_whitney_homology_left.
- apply module_hom_ext => x; exact: alexander_whitney_homology_right.
Defined.
Lemma alexander_whitney_homology_iso_hom (X : bisimplicial_set) n x :
  module_hom_fun (iso_hom (alexander_whitney_homology_iso X n)) x = homology_map (alexander_whitney R X) n x.
Proof. reflexivity. Qed.

Theorem alexander_whitney_quasi_isomorphism (X : bisimplicial_set) :
  quasi_isomorphism (alexander_whitney R X).
Proof.
move=> n; split.
- move=> x y h; rewrite -[x](@alexander_whitney_homology_left X n x)
    -[y](@alexander_whitney_homology_left X n y); by rewrite h.
- move=> y; exists (homology_map (alexander_whitney_inverse X) n y).
  exact: alexander_whitney_homology_right.
Qed.

Lemma alexander_whitney_inverse_zero (X : bisimplicial_set) x :
  chain_map_at (alexander_whitney_inverse X) 0%N x = @aw_zero_inverse R X x.
Proof. reflexivity. Qed.
End Equivalence.
End DPAlexanderWhitneyEquivalencePoly.
