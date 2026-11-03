(** Actual native nerve-chain homotopy from an ordinary natural transformation. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialChains SimplicialChainsMaps CategoryNerve CategoryStringChains CategoryStringChainsMaps CategoryStringChainHomotopy CategoryNerveStringChainTerms CategoryNerveStringChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve DPCategoryStringChainHomotopy.
Local Open Scope ring_scope.
Module DPCategoryNerveNatTransHomotopy.
Section Homotopy.
Variable R : pzRingType.
Variables C D : category.
Variables f g : functor C D.
Variable a : nat_trans f g.
Definition nerve_prism_at n : {linear term R (nerve C) n -> term R (nerve D) n.+1} :=
 (string_to_nerve_at R D n.+1 \o (@prism_chain_at R C D f g a n : {linear _ -> _}) \o nerve_to_string_at R C n : {linear _ -> _}).
Lemma nerve_prism_zero x :
 @DPSimplicialChains.boundary R (nerve D) 0%N (nerve_prism_at 0%N x)=
 map_at R (nerve_map g) 0%N x-map_at R (nerve_map f) 0%N x.
Proof.
change (@DPSimplicialChains.boundary R (nerve D) 0%N
 (string_to_nerve_at R D 1%N (@prism_chain_at R C D f g a 0%N (nerve_to_string_at R C 0%N x)))=map_at R (nerve_map g) 0%N x-map_at R (nerve_map f) 0%N x).
rewrite string_to_nerve_boundary prism_chain_zero linearB.
change (string_to_nerve_at R D 0%N (category_string_map_at R g 0%N (nerve_to_string_at R C 0%N x))-
 string_to_nerve_at R D 0%N (category_string_map_at R f 0%N (nerve_to_string_at R C 0%N x))=map_at R (nerve_map g) 0%N x-map_at R (nerve_map f) 0%N x).
by rewrite !string_to_nerve_naturality !string_to_nerve_inverse.
Qed.
Lemma nerve_prism_succ n x :
 @DPSimplicialChains.boundary R (nerve D) n.+1 (nerve_prism_at n.+1 x)+
 nerve_prism_at n (@DPSimplicialChains.boundary R (nerve C) n x)=
 map_at R (nerve_map g) n.+1 x-map_at R (nerve_map f) n.+1 x.
Proof.
change (@DPSimplicialChains.boundary R (nerve D) n.+1
 (string_to_nerve_at R D n.+2 (@prism_chain_at R C D f g a n.+1 (nerve_to_string_at R C n.+1 x)))+
 string_to_nerve_at R D n.+1 (@prism_chain_at R C D f g a n (nerve_to_string_at R C n (@DPSimplicialChains.boundary R (nerve C) n x)))=map_at R (nerve_map g) n.+1 x-map_at R (nerve_map f) n.+1 x).
rewrite string_to_nerve_boundary -nerve_to_string_boundary -linearD.
change (string_to_nerve_at R D n.+1
 (@category_string_boundary R D n.+1 (@prism_chain_at R C D f g a n.+1 (nerve_to_string_at R C n.+1 x))+
 @prism_chain_at R C D f g a n (@category_string_boundary R C n (nerve_to_string_at R C n.+1 x)))=map_at R (nerve_map g) n.+1 x-map_at R (nerve_map f) n.+1 x).
rewrite prism_chain_succ linearB.
change (string_to_nerve_at R D n.+1 (category_string_map_at R g n.+1 (nerve_to_string_at R C n.+1 x))-
 string_to_nerve_at R D n.+1 (category_string_map_at R f n.+1 (nerve_to_string_at R C n.+1 x))=map_at R (nerve_map g) n.+1 x-map_at R (nerve_map f) n.+1 x).
by rewrite !string_to_nerve_naturality !string_to_nerve_inverse.
Qed.
Definition nerve_nat_trans_homotopy : chain_homotopy (chain_map_of R (nerve_map g)) (chain_map_of R (nerve_map f)) :=
 @ChainHomotopy R (chains R (nerve C)) (chains R (nerve D)) (chain_map_of R (nerve_map g)) (chain_map_of R (nerve_map f))
 nerve_prism_at nerve_prism_zero nerve_prism_succ.
End Homotopy.
End DPCategoryNerveNatTransHomotopy.
