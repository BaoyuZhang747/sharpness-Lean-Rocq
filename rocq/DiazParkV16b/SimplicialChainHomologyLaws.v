(** Native homology functor laws for the actual simplicial chain maps. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism SimplicialSet SimplicialChains SimplicialChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.
Module DPSimplicialChainHomologyLaws.
Section Laws.
Variable R : pzRingType.
Lemma simplicial_homology_identity X n (x : homology (chains R X) n) :
 homology_map (chain_map_of R (nat_id X)) n x=x.
Proof.
have [z <-] := quotient_pi_surjective x; rewrite homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
change (map_at R (nat_id X) n (val z)=val z); exact: map_identity.
Qed.
Lemma simplicial_homology_composition X Y Z (f:simplicial_map X Y) (g:simplicial_map Y Z) n (x:homology (chains R X) n) :
 homology_map (chain_map_of R (nat_comp f g)) n x=
 homology_map (chain_map_of R g) n (homology_map (chain_map_of R f) n x).
Proof.
have [z <-] := quotient_pi_surjective x; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
change (map_at R (nat_comp f g) n (val z)=map_at R g n (map_at R f n (val z))).
exact: map_composition.
Qed.
End Laws.
End DPSimplicialChainHomologyLaws.
