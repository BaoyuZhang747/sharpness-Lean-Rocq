(** Signed native opposite reversal commutes with every actual functor map. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryIsomorphism BarPaths BarFreeModule.
From DiazParkV16b Require Import SimplexCategory CategoryNervePaths CategoryNervePathsNaturality
  CategoryNerveOpposite CategoryStringOppositePaths CategoryStringOppositeUnsigned
  CategoryStringOppositeChains CategoryBarPullbackPaths CategoryStringChains CategoryStringChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPCategoryBarPullback DPCategoryNervePathEquivalence
  DPCategoryNervePathNaturality DPCategoryNerveOpposite DPCategoryStringOppositePaths.
Local Open Scope ring_scope.

Module DPCategoryStringOppositeNaturality.
Section Naturality.
Variables C D : category.
Variable F : functor C D.

Lemma reverse_nerve_postcompose n (T : functor (DPSimplexCategory.ordinal_category n) C) :
  reverse_nerve (functor_comp T F) = functor_comp (reverse_nerve T) (functor_op F).
Proof.
apply (@functor_extensionality (DPSimplexCategory.ordinal_category n) (opposite D)
  (reverse_nerve (functor_comp T F)) (functor_comp (reverse_nerve T) (functor_op F)) Logic.eq_refl).
reflexivity.
Qed.

Lemma reverse_path_naturality n (p : @DiazParkBarPaths.path C n) :
  reverse_path (path_map F n p) = path_map (functor_op F) n (reverse_path p).
Proof.
by rewrite /reverse_path path_nerve_map reverse_nerve_postcompose nerve_path_postcompose.
Qed.

Variable R : pzRingType.

Lemma unsigned_reverse_naturality n (v : category_string_term R C n) :
  DPCategoryStringOppositeUnsigned.reverse_at R D n (category_string_map_at R F n v) =
  category_string_map_at R (functor_op F) n (DPCategoryStringOppositeUnsigned.reverse_at R C n v).
Proof.
apply (free_lift_ext
  (g := (DPCategoryStringOppositeUnsigned.reverse_at R D n \o category_string_map_at R F n : {linear _ -> _}))
  (h := (category_string_map_at R (functor_op F) n \o DPCategoryStringOppositeUnsigned.reverse_at R C n : {linear _ -> _}))).
move=> s; by rewrite /= /DPCategoryStringOppositeUnsigned.reverse_at /category_string_map_at
  !free_map_basis reverse_path_naturality.
Qed.

Theorem reverse_naturality n (v : category_string_term R C n) :
  DPCategoryStringOppositeChains.reverse_at R D n (category_string_map_at R F n v) =
  category_string_map_at R (functor_op F) n (DPCategoryStringOppositeChains.reverse_at R C n v).
Proof. by rewrite /DPCategoryStringOppositeChains.reverse_at linearZ unsigned_reverse_naturality. Qed.

Theorem unreverse_naturality n (v : category_string_term R (opposite C) n) :
  DPCategoryStringOppositeChains.unreverse_at R D n (category_string_map_at R (functor_op F) n v) =
  category_string_map_at R F n (DPCategoryStringOppositeChains.unreverse_at R C n v).
Proof.
apply (can_inj (@DPCategoryStringOppositeChains.reverse_inverse R D n)).
by rewrite DPCategoryStringOppositeChains.unreverse_inverse reverse_naturality
  DPCategoryStringOppositeChains.unreverse_inverse.
Qed.
End Naturality.
End DPCategoryStringOppositeNaturality.
