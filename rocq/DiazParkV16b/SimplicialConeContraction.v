(** Explicit cone operators give an augmented contraction of native simplicial chains.
    The only premises are the displayed face identities of the actual operators. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialSetOperators SimplicialChains ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplicialSet DPSimplicialOperators DPSimplicialChains DPChainComplex.
Local Open Scope ring_scope.

Module DPSimplicialConeContraction.
Section Cone.
Variable R : pzRingType.
Variable X : simplicial_set.
Variable cone : forall n, simplex X n -> simplex X n.+1.
Arguments cone n _ : clear implicits.
Hypothesis cone_face_zero : forall n x, @indexed_face X n 0 (cone n x) = x.
Hypothesis cone_face_successor : forall n (i : 'I_n.+2) x,
  @indexed_face X n.+1 i.+1 (cone n.+1 x) = cone n (@indexed_face X n i x).

Definition cone_map n : {linear term R X n -> term R X n.+1} := free_map R (cone n).
Lemma cone_map_basis n x : cone_map n (free_basis R x) = free_basis R (cone n x).
Proof. exact: free_map_basis. Qed.
Lemma cone_map_face_zero n (a : term R X n) : face_map R X n 0 (cone_map n a) = a.
Proof.
apply: (free_lift_ext (g := (face_map R X n 0 \o cone_map n : {linear _ -> _}))
  (h := (idfun : {linear term R X n -> term R X n}))).
move=> x; rewrite /= cone_map_basis /face_map free_map_basis cone_face_zero; reflexivity.
Qed.
Lemma cone_map_face_successor n (i : 'I_n.+2) (a : term R X n.+1) :
  face_map R X n.+1 i.+1 (cone_map n.+1 a) = cone_map n (face_map R X n i a).
Proof.
apply: (free_lift_ext (g := (face_map R X n.+1 i.+1 \o cone_map n.+1 : {linear _ -> _}))
  (h := (cone_map n \o face_map R X n i : {linear _ -> _}))).
move=> x; rewrite /= cone_map_basis /face_map !free_map_basis.
congr (free_basis R _); exact: cone_face_successor.
Qed.
Theorem cone_contraction_successor n (a : term R X n.+1) :
  @DPSimplicialChains.boundary R X n.+1 (cone_map n.+1 a) +
    cone_map n (@DPSimplicialChains.boundary R X n a) = a.
Proof.
rewrite /DPSimplicialChains.boundary big_ord_recl expr0 scale1r cone_map_face_zero linear_sum.
have he : \sum_(i < n.+2) (-1 : R)^+i.+1 *: face_map R X n.+1 i.+1 (cone_map n.+1 a) =
    - (\sum_(i < n.+2) cone_map n ((-1 : R)^+i *: face_map R X n i a)).
  rewrite -sumrN; apply: eq_bigr => i _.
  rewrite cone_map_face_successor linearZ exprS mulN1r scaleNr; reflexivity.
rewrite he; exact: subrK.
Qed.
Theorem cone_positive_exact n (a : chain_term (chains R X) n.+1) :
  @cycle R (chains R X) n.+1 a -> @DPChainComplex.boundary R (chains R X) n.+1 a.
Proof.
move=> ha; exists (cone_map n.+1 a).
have h := cone_contraction_successor a.
change (@DPSimplicialChains.boundary R X n a = 0) in ha.
by rewrite ha linear0 addr0 in h.
Qed.

Section Augmentation.
Variable A : lmodType R.
Variable epsilon : {linear term R X 0%N -> A}.
Variable section : {linear A -> term R X 0%N}.
Hypothesis cone_last : forall x,
  free_basis R (@indexed_face X 0 1 (cone 0 x)) = section (epsilon (free_basis R x)).
Lemma cone_map_last (a : term R X 0%N) :
  face_map R X 0 1 (cone_map 0 a) = section (epsilon a).
Proof.
apply: (free_lift_ext (g := (face_map R X 0 1 \o cone_map 0 : {linear _ -> _}))
  (h := (section \o epsilon : {linear _ -> _}))).
move=> x; rewrite /= cone_map_basis /face_map free_map_basis; exact: cone_last.
Qed.
Theorem cone_contraction_zero (a : term R X 0%N) :
  @DPSimplicialChains.boundary R X 0 (cone_map 0 a) + section (epsilon a) = a.
Proof.
rewrite /DPSimplicialChains.boundary !big_ord_recl big_ord0 expr0 expr1 scale1r scaleN1r
  cone_map_face_zero cone_map_last addr0; exact: subrK.
Qed.
Theorem cone_augmentation_exact (a : term R X 0%N) :
  epsilon a = 0 -> @DPChainComplex.boundary R (chains R X) 0 a.
Proof.
move=> ha; exists (cone_map 0 a).
have h := cone_contraction_zero a; by rewrite ha linear0 addr0 in h.
Qed.
End Augmentation.
End Cone.
End DPSimplicialConeContraction.
