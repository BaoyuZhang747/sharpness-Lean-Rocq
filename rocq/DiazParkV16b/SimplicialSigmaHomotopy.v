(** Native chain homotopies assemble over arbitrary disjoint simplicial families. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialChains SimplicialChainsMaps SimplicialSigma.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps DPSimplicialSigma.
Local Open Scope ring_scope.
Module DPSimplicialSigmaHomotopy.
Section Homotopy.
Variable R : pzRingType.
Variable I : Type.
Variables X Y : I -> simplicial_set.
Variables f g : forall i, simplicial_map (X i) (Y i).
Variable h : forall i, chain_homotopy (chain_map_of R (f i)) (chain_map_of R (g i)).
Definition sigma_homotopy_at n : {linear term R (sigma_set X) n -> term R (sigma_set Y) n.+1} :=
 (free_lift (fun z : {i:I & simplex (X i) n} => match z with existT i x=>
 map_at R (sigma_inclusion Y i) n.+1 (chain_homotopy_at (h i) n (free_basis R x)) end) : {linear _ -> _}).
Lemma sigma_homotopy_inclusion n i (x : term R (X i) n) :
 sigma_homotopy_at n (map_at R (sigma_inclusion X i) n x)=
 map_at R (sigma_inclusion Y i) n.+1 (chain_homotopy_at (h i) n x).
Proof.
apply (free_lift_ext
 (g := (sigma_homotopy_at n \o map_at R (sigma_inclusion X i) n : {linear _ -> _}))
 (h := (map_at R (sigma_inclusion Y i) n.+1 \o chain_homotopy_at (h i) n : {linear _ -> _}))).
move=>b.
change (sigma_homotopy_at n (map_at R (sigma_inclusion X i) n (free_basis R b))=
 map_at R (sigma_inclusion Y i) n.+1 (chain_homotopy_at (h i) n (free_basis R b))).
rewrite map_at_basis /sigma_homotopy_at; exact: free_lift_basis.
Qed.
Lemma sigma_map_inclusion_at (a:forall i,simplicial_map (X i) (Y i)) n i (x : term R (X i) n) :
 map_at R (sigma_map a) n (map_at R (sigma_inclusion X i) n x)=
 map_at R (sigma_inclusion Y i) n (map_at R (a i) n x).
Proof. by rewrite -!map_composition sigma_map_inclusion. Qed.
Lemma sigma_homotopy_zero_basis i (x : simplex (X i) 0%N) :
 @boundary R (sigma_set Y) 0%N (sigma_homotopy_at 0%N (free_basis R (existT _ i x)))=
 map_at R (sigma_map f) 0%N (free_basis R (existT _ i x))-
 map_at R (sigma_map g) 0%N (free_basis R (existT _ i x)).
Proof.
have e : free_basis R (existT _ i x)=map_at R (sigma_inclusion X i) 0%N (free_basis R x) by rewrite map_at_basis.
rewrite e sigma_homotopy_inclusion map_boundary !sigma_map_inclusion_at.
have hh := chain_homotopy_zero (h i) (free_basis R x).
rewrite hh linearB; reflexivity.
Qed.
Lemma sigma_homotopy_succ_basis n i (x : simplex (X i) n.+1) :
 @boundary R (sigma_set Y) n.+1 (sigma_homotopy_at n.+1 (free_basis R (existT _ i x)))+
 sigma_homotopy_at n (@boundary R (sigma_set X) n (free_basis R (existT _ i x)))=
 map_at R (sigma_map f) n.+1 (free_basis R (existT _ i x))-
 map_at R (sigma_map g) n.+1 (free_basis R (existT _ i x)).
Proof.
have e : free_basis R (existT _ i x)=map_at R (sigma_inclusion X i) n.+1 (free_basis R x) by rewrite map_at_basis.
rewrite e !sigma_homotopy_inclusion !map_boundary sigma_homotopy_inclusion !sigma_map_inclusion_at -linearD.
change (map_at R (sigma_inclusion Y i) n.+1
 (@boundary R (Y i) n.+1 (chain_homotopy_at (h i) n.+1 (free_basis R x))+
 chain_homotopy_at (h i) n (@boundary R (X i) n (free_basis R x)))=
 map_at R (sigma_inclusion Y i) n.+1 (map_at R (f i) n.+1 (free_basis R x))-
 map_at R (sigma_inclusion Y i) n.+1 (map_at R (g i) n.+1 (free_basis R x))).
rewrite (@chain_homotopy_succ R _ _ _ _ (h i) n (free_basis R x)) linearB; reflexivity.
Qed.
Lemma sigma_homotopy_zero x :
 @boundary R (sigma_set Y) 0%N (sigma_homotopy_at 0%N x)=
 map_at R (sigma_map f) 0%N x-map_at R (sigma_map g) 0%N x.
Proof.
apply (free_lift_ext
 (g := (@boundary R (sigma_set Y) 0%N \o sigma_homotopy_at 0%N : {linear _ -> _}))
 (h := (map_at R (sigma_map f) 0%N \- map_at R (sigma_map g) 0%N : {linear _ -> _}))).
move=>[i a]; exact: sigma_homotopy_zero_basis.
Qed.
Lemma sigma_homotopy_succ n x :
 @boundary R (sigma_set Y) n.+1 (sigma_homotopy_at n.+1 x)+sigma_homotopy_at n (@boundary R (sigma_set X) n x)=
 map_at R (sigma_map f) n.+1 x-map_at R (sigma_map g) n.+1 x.
Proof.
apply (free_lift_ext
 (g := ((@boundary R (sigma_set Y) n.+1 \o sigma_homotopy_at n.+1) \+
 (sigma_homotopy_at n \o @boundary R (sigma_set X) n) : {linear _ -> _}))
 (h := (map_at R (sigma_map f) n.+1 \- map_at R (sigma_map g) n.+1 : {linear _ -> _}))).
move=>[i a]; exact: sigma_homotopy_succ_basis.
Qed.
Definition sigma_chain_homotopy : chain_homotopy (chain_map_of R (sigma_map f)) (chain_map_of R (sigma_map g)) :=
 @ChainHomotopy R (chains R (sigma_set X)) (chains R (sigma_set Y))
 (chain_map_of R (sigma_map f)) (chain_map_of R (sigma_map g)) sigma_homotopy_at sigma_homotopy_zero sigma_homotopy_succ.
End Homotopy.
End DPSimplicialSigmaHomotopy.
