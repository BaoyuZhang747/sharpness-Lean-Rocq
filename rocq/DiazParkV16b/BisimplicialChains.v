(** The actual free chain bicomplex of an arbitrary bisimplicial set. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplexCategoryOperators
  SimplicialSet SimplicialSetOperators SimplicialChains SimplicialChainsMaps BisimplicialSet
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplicialTypes DPSimplexCategory DPSimplexOperators
  DPSimplicialSet DPSimplicialOperators DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet
  DPFirstQuadrantChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPBisimplicialChains.
Definition horizontal_simplicial (X : bisimplicial_set) (q : nat) : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category (fun p => bisimplex X p q)
  (fun p m f => horizontal_map X f q) _ _).
- move=> p; apply type_morphism_ext => x; exact: horizontal_map_identity.
- move=> p m k f g; apply type_morphism_ext => x; exact: horizontal_map_compose.
Defined.

Section Chains.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Definition bi_term p q := free_module R (bisimplex X p q).
Definition horizontal_d p q (a : bi_term p.+1 q) : bi_term p q :=
  \sum_(i < p.+2) (-1)^+i *: map_at R (fmap X (coface (inord i))) q a.
Arguments horizontal_d p q a : clear implicits.
Lemma horizontal_d_linear p q : linear (@horizontal_d p q).
Proof.
move=> r a b; rewrite /horizontal_d scaler_sumr -big_split.
apply eq_bigr => i _; by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ p q := GRing.isLinear.Build R _ _ _ (@horizontal_d p q) (@horizontal_d_linear p q).

Lemma horizontal_d_native p q a : horizontal_d p q a = @boundary R (horizontal_simplicial X q) p a.
Proof. reflexivity. Qed.
Definition vertical_d p q : {linear bi_term p q.+1 -> bi_term p q} :=
  @boundary R (fobj X p) q.

Lemma horizontal_d_squared p q a : horizontal_d p q (horizontal_d p.+1 q a) = 0.
Proof. exact (@boundary_squared R (horizontal_simplicial X q) p a). Qed.
Lemma vertical_d_squared p q a : vertical_d p q (vertical_d p q.+1 a) = 0.
Proof. exact (@boundary_squared R (fobj X p) q a). Qed.
Lemma horizontal_vertical_d p q a :
  horizontal_d p q (vertical_d p.+1 q a) = vertical_d p q (horizontal_d p q.+1 a).
Proof.
rewrite /horizontal_d linear_sum; apply eq_bigr => i _.
rewrite linearZ; congr (_ *: _); symmetry; exact: map_boundary.
Qed.

Definition bisimplicial_bicomplex : bicomplex R :=
  @Bicomplex R bi_term (fun p q => (@horizontal_d p q : {linear _ -> _})) vertical_d
    horizontal_d_squared vertical_d_squared horizontal_vertical_d.
Definition diagonal_chains := chains R (diagonal X).
Definition total_chains := total_complex bisimplicial_bicomplex.
End Chains.
End DPBisimplicialChains.
