(** Actual inverse chain maps between functor simplices of the nerve and
    category strings. The face compatibility is the independently constructed
    ordinal/path theorem; no comparison premise is assumed. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSetOperators
  SimplicialChains CategoryNerve CategoryNervePaths CategoryNervePathsFaces
  CategoryStringChains CategoryNerveStringChainTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPCategoryNerve
  DPCategoryNervePathEquivalence DPCategoryNervePathFaces.
Local Open Scope ring_scope.

Section Chains.
Variable R : pzRingType.
Variable C : category.

Lemma nerve_to_string_face n i (hi : (i < n.+2)%N)
    (v : DPSimplicialChains.term R (nerve C) n.+1) :
    @category_string_face R C n i (nerve_to_string_at R C n.+1 v) =
    nerve_to_string_at R C n (DPSimplicialChains.face_map R (nerve C) n i v).
Proof.
apply (free_lift_ext
  (g := (@category_string_face R C n i \o nerve_to_string_at R C n.+1 : {linear _ -> _}))
  (h := (nerve_to_string_at R C n \o DPSimplicialChains.face_map R (nerve C) n i : {linear _ -> _}))).
intro s; rewrite /= /category_string_face /nerve_to_string_at
  /DPSimplicialChains.face_map !free_map_basis /DPSimplicialChains.indexed_face.
rewrite nerve_path_face.
have he : val (inord i : 'I_n.+2) = i by exact: inordK.
by rewrite he.
Qed.

Lemma nerve_to_string_boundary n (v : DPSimplicialChains.term R (nerve C) n.+1) :
    @category_string_boundary R C n (nerve_to_string_at R C n.+1 v) =
    nerve_to_string_at R C n (@DPSimplicialChains.boundary R (nerve C) n v).
Proof.
rewrite /category_string_boundary /DPSimplicialChains.boundary linear_sum.
apply eq_bigr; intros i _; rewrite linearZ.
by rewrite nerve_to_string_face //; exact: ltn_ord.
Qed.

Definition nerve_to_string_chain :
    chain_map (DPSimplicialChains.chains R (nerve C)) (category_string_chain R C) :=
  @ChainMap R (DPSimplicialChains.chains R (nerve C)) (category_string_chain R C)
    (nerve_to_string_at R C) nerve_to_string_boundary.

Lemma string_to_nerve_boundary n (v : category_string_term R C n.+1) :
    @DPSimplicialChains.boundary R (nerve C) n (string_to_nerve_at R C n.+1 v) =
    string_to_nerve_at R C n (@category_string_boundary R C n v).
Proof.
apply (can_inj (@string_to_nerve_inverse R C n)).
by rewrite -nerve_to_string_boundary !nerve_to_string_inverse.
Qed.

Definition string_to_nerve_chain :
    chain_map (category_string_chain R C) (DPSimplicialChains.chains R (nerve C)) :=
  @ChainMap R (category_string_chain R C) (DPSimplicialChains.chains R (nerve C))
    (string_to_nerve_at R C) string_to_nerve_boundary.

Theorem nerve_string_chain_inverse n (v : category_string_term R C n) :
    chain_map_at (chain_composition string_to_nerve_chain nerve_to_string_chain) n v = v.
Proof. exact: nerve_to_string_inverse. Qed.

Theorem string_nerve_chain_inverse n (v : DPSimplicialChains.term R (nerve C) n) :
    chain_map_at (chain_composition nerve_to_string_chain string_to_nerve_chain) n v = v.
Proof. exact: string_to_nerve_inverse. Qed.
End Chains.
