(** Actual inverses and native homology isomorphisms for degreewise bijective chain maps. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPChainComplex DPChainHomology DPChainHomologyMaps.
Local Open Scope ring_scope.

Module DPChainDegreewiseIso.
Section Inverse.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable hi : forall n, injective (chain_map_at f n).
Variable hs : forall n y, exists x, chain_map_at f n x = y.

Definition degree_iso n : @isomorphism (module_category R) (chain_term C n) (chain_term D n) :=
  linear_bijection_iso (@hi n) (@hs n).
Definition inverse_at n : {linear chain_term D n -> chain_term C n} :=
  module_hom_to_linear (iso_inv (degree_iso n)).

Lemma inverse_at_right n y : chain_map_at f n (inverse_at n y) = y.
Proof. exact: module_iso_inv_hom_apply. Qed.
Lemma inverse_at_left n x : inverse_at n (chain_map_at f n x) = x.
Proof. exact: module_iso_hom_inv_apply. Qed.

Definition inverse_chain : chain_map D C.
Proof.
refine (@ChainMap R D C inverse_at _).
move=> n y; apply: (@hi n).
by rewrite -chain_map_commutes !inverse_at_right.
Defined.

Lemma inverse_chain_right n y : chain_map_at f n (chain_map_at inverse_chain n y) = y.
Proof. exact: inverse_at_right. Qed.
Lemma inverse_chain_left n x : chain_map_at inverse_chain n (chain_map_at f n x) = x.
Proof. exact: inverse_at_left. Qed.

Lemma inverse_homology_right n (q : homology D n) :
  homology_map f n (homology_map inverse_chain n q) = q.
Proof.
have [z <-] := quotient_pi_surjective q; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
change (chain_map_at f n (chain_map_at inverse_chain n (val z)) = val z).
exact: inverse_chain_right.
Qed.

Lemma inverse_homology_left n (q : homology C n) :
  homology_map inverse_chain n (homology_map f n q) = q.
Proof.
have [z <-] := quotient_pi_surjective q; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
change (chain_map_at inverse_chain n (chain_map_at f n (val z)) = val z).
exact: inverse_chain_left.
Qed.

Definition degreewise_homology_iso n : @isomorphism (module_category R) (homology C n) (homology D n).
Proof.
refine (@Build_isomorphism (module_category R) (homology C n) (homology D n)
  (module_hom_of_linear (homology_map f n)) (module_hom_of_linear (homology_map inverse_chain n)) _ _).
- apply module_hom_ext => x; exact: inverse_homology_left.
- apply module_hom_ext => y; exact: inverse_homology_right.
Defined.

Lemma degreewise_homology_iso_hom n (q : homology C n) :
  module_hom_fun (iso_hom (degreewise_homology_iso n)) q = homology_map f n q.
Proof. reflexivity. Qed.
End Inverse.
End DPChainDegreewiseIso.
