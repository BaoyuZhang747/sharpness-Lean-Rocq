(** An explicit augmented contraction of actual unnormalized simplex chains. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators SimplicialChains ChainComplex StandardSimplexCone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPStandardSimplexConeChains.
Import DiazParkFreeModule DPSimplexCategory DPSimplexOperators DPSimplexIdentities
  DPSimplicialSet DPSimplicialOperators DPSimplicialChains DPChainComplex DPStandardSimplexCone.

Lemma indexed_cone_zero d n (f : ordinal_map n d) :
  @indexed_face (standard_simplex d) n 0 (cone f) = f.
Proof.
have e : (inord 0 : 'I_n.+2) = ord0 by apply val_inj; exact: inordK.
change (ordinal_map_compose (coface (inord 0)) (cone f) = f).
rewrite e; exact: cone_face_zero.
Qed.

Lemma indexed_cone_successor d n (i : 'I_n.+2) (f : ordinal_map n.+1 d) :
  @indexed_face (standard_simplex d) n.+1 i.+1 (cone f) =
    cone (@indexed_face (standard_simplex d) n i f).
Proof.
have e : (inord i : 'I_n.+2) = i by apply val_inj; exact: inordK.
have es : (inord i.+1 : 'I_n.+3) = vertex_successor i.
  apply val_inj. change (nat_of_ord (inord i.+1 : 'I_n.+3) = i.+1). apply: inordK. exact: ltn_ord i.
change (ordinal_map_compose (coface (inord i.+1)) (cone f) =
  cone (ordinal_map_compose (coface (inord i)) f)).
rewrite e es; exact: cone_face_successor.
Qed.

Lemma indexed_cone_last_zero d (f : ordinal_map 0 d) :
  @indexed_face (standard_simplex d) 0 1 (cone f) = zero_vertex d.
Proof.
have e : (inord 1 : 'I_2) = vertex_successor (@ord0 0) by apply val_inj; exact: inordK.
change (ordinal_map_compose (coface (inord 1)) (cone f) = zero_vertex d).
rewrite e; exact: cone_face_last_zero.
Qed.

Section Chains.
Variable R : pzRingType.
Variable d : nat.
Let X := standard_simplex d.

Definition cone_map n : {linear term R X n -> term R X n.+1} := free_map R (@cone n d).

Lemma cone_map_basis n (f : ordinal_map n d) :
  cone_map n (free_basis R f) = free_basis R (cone f).
Proof. exact: free_map_basis. Qed.

Lemma cone_map_face_zero n (a : term R X n) : face_map R X n 0 (cone_map n a) = a.
Proof.
apply: (free_lift_ext (g := (face_map R X n 0 \o cone_map n : {linear _ -> _}))
  (h := (idfun : {linear term R X n -> term R X n}))).
move=> f. change (face_map R X n 0 (cone_map n (free_basis R f)) = free_basis R f).
rewrite cone_map_basis /face_map free_map_basis.
change (free_basis R (@indexed_face (standard_simplex d) n 0 (cone f)) = free_basis R f).
by rewrite indexed_cone_zero.
Qed.

Lemma cone_map_face_successor n (i : 'I_n.+2) (a : term R X n.+1) :
  face_map R X n.+1 i.+1 (cone_map n.+1 a) = cone_map n (face_map R X n i a).
Proof.
apply: (free_lift_ext (g := (face_map R X n.+1 i.+1 \o cone_map n.+1 : {linear _ -> _}))
  (h := (cone_map n \o face_map R X n i : {linear _ -> _}))).
move=> f; rewrite /= cone_map_basis /face_map !free_map_basis.
congr (free_basis R _); exact: indexed_cone_successor.
Qed.

Theorem simplex_contraction_successor n (a : term R X n.+1) :
  @DPSimplicialChains.boundary R X n.+1 (cone_map n.+1 a) +
    cone_map n (@DPSimplicialChains.boundary R X n a) = a.
Proof.
rewrite /DPSimplicialChains.boundary big_ord_recl expr0 scale1r cone_map_face_zero linear_sum.
have he : \sum_(i < n.+2) (-1 : R)^+i.+1 *:
    face_map R X n.+1 i.+1 (cone_map n.+1 a) =
    - (\sum_(i < n.+2) cone_map n ((-1 : R)^+i *: face_map R X n i a)).
  rewrite -sumrN; apply: eq_bigr => i _.
  rewrite cone_map_face_successor linearZ exprS mulN1r scaleNr. reflexivity.
rewrite he; exact: subrK.
Qed.

Definition simplex_augmentation_section (r : R^o) : term R X 0%N :=
  (r : R) *: free_basis R (zero_vertex d).

Lemma simplex_augmentation_section_linear : linear simplex_augmentation_section.
Proof. move=> a x y; by rewrite /simplex_augmentation_section scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _
  simplex_augmentation_section simplex_augmentation_section_linear.

Lemma simplex_augmentation_sectionK r : augmentation R X (simplex_augmentation_section r) = r.
Proof. rewrite /simplex_augmentation_section linearZ augmentation_basis. exact: mulr1. Qed.

Lemma cone_map_face_last_zero (a : term R X 0%N) :
  face_map R X 0 1 (cone_map 0 a) = simplex_augmentation_section (augmentation R X a).
Proof.
apply: (free_lift_ext (g := (face_map R X 0 1 \o cone_map 0 : {linear _ -> _}))
  (h := (simplex_augmentation_section \o augmentation R X : {linear _ -> _}))).
move=> f.
change (face_map R X 0 1 (cone_map 0 (free_basis R f)) = simplex_augmentation_section (augmentation R X (free_basis R f))).
rewrite cone_map_basis /face_map free_map_basis augmentation_basis /simplex_augmentation_section scale1r.
change (free_basis R (@indexed_face (standard_simplex d) 0 1 (cone f)) = free_basis R (zero_vertex d)).
by rewrite indexed_cone_last_zero.
Qed.

Theorem simplex_contraction_zero (a : term R X 0%N) :
  @DPSimplicialChains.boundary R X 0 (cone_map 0 a) +
    simplex_augmentation_section (augmentation R X a) = a.
Proof.
rewrite /DPSimplicialChains.boundary !big_ord_recl big_ord0 expr0 expr1 scale1r scaleN1r
  cone_map_face_zero cone_map_face_last_zero addr0. exact: subrK.
Qed.

Theorem standard_simplex_positive_exact n (a : chain_term (chains R X) n.+1) :
  @cycle R (chains R X) n.+1 a -> @DPChainComplex.boundary R (chains R X) n.+1 a.
Proof.
move=> ha; exists (cone_map n.+1 a).
have h := simplex_contraction_successor a.
change (@DPSimplicialChains.boundary R X n a = 0) in ha.
by rewrite ha linear0 addr0 in h.
Qed.

Theorem standard_simplex_augmentation_exact (a : term R X 0%N) :
  augmentation R X a = 0 -> @DPChainComplex.boundary R (chains R X) 0 a.
Proof.
move=> ha; exists (cone_map 0 a).
have h := simplex_contraction_zero a. by rewrite ha linear0 addr0 in h.
Qed.

End Chains.
End DPStandardSimplexConeChains.
