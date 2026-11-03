(** Actual relative-chain isomorphism of the skeletal attaching pushout. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialChainsMaps
  SimplicialSkeletonAttachmentCover SimplicialSkeletonAttachmentDegreewise
  ChainComplex ChainSubcomplex ChainMapImage ChainRelativePairs
  ChainQuasiIsomorphism ChainQuasiIsomorphismLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainSubcomplex DPChainMapImage
  DPChainRelativePairs DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPSimplicialSet DPSimplicialChains DPSimplicialChainMaps
  DPSimplicialAttachmentCover DPSimplicialAttachmentDegreewise.
Local Open Scope ring_scope.

Module DPSimplicialAttachmentRelativeChains.
Section Attachment.
Variable R : pzRingType.
Variable X : simplicial_set.
Variable n : nat.
Let i := chain_map_of R (attaching_inclusion X n).
Let j := chain_map_of R (attaching_stage X n).
Let u := chain_map_of R (attaching_map X n).
Let v := chain_map_of R (attaching_cells X n).
Let C := relative_chain i.
Let D := relative_chain j.

Lemma attachment_chain_square k x :
  chain_map_at v k (chain_map_at i k x) = chain_map_at j k (chain_map_at u k x).
Proof.
change (map_at R (attaching_cells X n) k (map_at R (attaching_inclusion X n) k x) =
  map_at R (attaching_stage X n) k (map_at R (attaching_map X n) k x)).
by rewrite -!map_composition attaching_square.
Qed.
Definition attachment_relative_map : chain_map C D := relative_pair_map attachment_chain_square.
Lemma attachment_relative_map_projection k x :
  chain_map_at attachment_relative_map k (chain_map_at (relative_projection i) k x) =
    chain_map_at (relative_projection j) k (chain_map_at v k x).
Proof. exact: relative_pair_map_projection. Qed.

Definition attachment_inverse_basis k : simplex (stage_set X n.+1) k -> chain_term C k :=
  @attaching_degree_desc X n k (chain_term C k) (fun _ => 0)
    (fun x => chain_map_at (relative_projection i) k (free_basis R x)).
Lemma attachment_inverse_boundary k (c : simplex (boundary_copower X n) k) :
  (0 : chain_term C k) = chain_map_at (relative_projection i) k
    (free_basis R (component (attaching_inclusion X n) k c)).
Proof.
rewrite -map_at_basis; symmetry; exact: relative_projection_annihilates.
Qed.
Lemma attachment_inverse_basis_old k x :
  attachment_inverse_basis (component (attaching_stage X n) k x) = 0.
Proof. exact: (attaching_degree_desc_old (@attachment_inverse_boundary k)). Qed.
Lemma attachment_inverse_basis_cell k x :
  attachment_inverse_basis (component (attaching_cells X n) k x) =
    chain_map_at (relative_projection i) k (free_basis R x).
Proof. exact: (attaching_degree_desc_cell (@attachment_inverse_boundary k)). Qed.
Definition attachment_inverse_lift k :
    {linear chain_term (chains R (stage_set X n.+1)) k -> chain_term C k} :=
  (free_lift (@attachment_inverse_basis k) : {linear _ -> _}).
Lemma attachment_inverse_lift_basis k x :
  attachment_inverse_lift k (free_basis R x) = attachment_inverse_basis x.
Proof. exact: free_lift_basis. Qed.
Lemma attachment_inverse_lift_old k x :
  attachment_inverse_lift k (chain_map_at j k x) = 0.
Proof.
rewrite -[x](free_basis_generation x) (linear_sum (chain_map_at j k))
  (linear_sum (attachment_inverse_lift k)).
apply: big1 => a _.
rewrite !linearZ.
change ((free_coefficient x a : R) *:
  attachment_inverse_lift k (map_at R (attaching_stage X n) k (free_basis R a)) = 0).
by rewrite map_at_basis attachment_inverse_lift_basis attachment_inverse_basis_old scaler0.
Qed.
Lemma attachment_inverse_lift_cell k x :
  attachment_inverse_lift k (chain_map_at v k x) = chain_map_at (relative_projection i) k x.
Proof.
apply: (free_lift_ext
  (g := (attachment_inverse_lift k \o chain_map_at v k : {linear _ -> _}))
  (h := chain_map_at (relative_projection i) k)).
move=> a.
change (attachment_inverse_lift k (map_at R (attaching_cells X n) k (free_basis R a)) =
  chain_map_at (relative_projection i) k (free_basis R a)).
by rewrite map_at_basis attachment_inverse_lift_basis attachment_inverse_basis_cell.
Qed.
Lemma attachment_inverse_kills k x :
  subspace_at (image_subcomplex j) k x -> attachment_inverse_lift k x = 0.
Proof. move=> [a <-]; exact: attachment_inverse_lift_old. Qed.
Definition attachment_inverse_at k : {linear chain_term D k -> chain_term C k} :=
  (@quotient_lift R (chain_term (chains R (stage_set X n.+1)) k)
    (subspace_at (image_subcomplex j) k) (chain_term C k) (attachment_inverse_lift k)
    (@attachment_inverse_kills k) : {linear _ -> _}).
Lemma attachment_inverse_projection k x :
  attachment_inverse_at k (chain_map_at (relative_projection j) k x) = attachment_inverse_lift k x.
Proof. exact: quotient_lift_pi. Qed.
Lemma attachment_relative_forwardK k x :
  attachment_inverse_at k (chain_map_at attachment_relative_map k x) = x.
Proof.
have [a <-] := @relative_projection_surjective R _ _ i k x.
by rewrite attachment_relative_map_projection attachment_inverse_projection attachment_inverse_lift_cell.
Qed.
Lemma attachment_relative_inverseK k x :
  chain_map_at attachment_relative_map k (attachment_inverse_at k x) = x.
Proof.
have [a <-] := @relative_projection_surjective R _ _ j k x.
rewrite attachment_inverse_projection.
apply: (free_lift_ext
  (g := (chain_map_at attachment_relative_map k \o attachment_inverse_lift k : {linear _ -> _}))
  (h := chain_map_at (relative_projection j) k)).
move=> y.
have [[z|z] hz] := attaching_cover_surjective y.
- change (component (attaching_stage X n) k z = y) in hz.
  rewrite -hz.
  change (chain_map_at attachment_relative_map k
    (attachment_inverse_lift k (free_basis R (component (attaching_stage X n) k z))) =
      chain_map_at (relative_projection j) k (free_basis R (component (attaching_stage X n) k z))).
  rewrite attachment_inverse_lift_basis attachment_inverse_basis_old linear0 -map_at_basis.
  symmetry; exact: relative_projection_annihilates.
- change (component (attaching_cells X n) k z = y) in hz.
  rewrite -hz.
  change (chain_map_at attachment_relative_map k
    (attachment_inverse_lift k (free_basis R (component (attaching_cells X n) k z))) =
      chain_map_at (relative_projection j) k (free_basis R (component (attaching_cells X n) k z))).
  rewrite attachment_inverse_lift_basis attachment_inverse_basis_cell attachment_relative_map_projection.
  change (chain_map_at (relative_projection j) k (map_at R (attaching_cells X n) k (free_basis R z)) =
    chain_map_at (relative_projection j) k (free_basis R (component (attaching_cells X n) k z))).
  by rewrite map_at_basis.
Qed.
Lemma attachment_relative_injective k : injective (chain_map_at attachment_relative_map k).
Proof. exact: (can_inj (attachment_relative_forwardK (k := k))). Qed.
Lemma attachment_inverse_commutes k x :
  chain_d C k (attachment_inverse_at k.+1 x) = attachment_inverse_at k (chain_d D k x).
Proof.
apply: attachment_relative_injective.
by rewrite -chain_map_commutes !attachment_relative_inverseK.
Qed.
Definition attachment_relative_inverse : chain_map D C :=
  @ChainMap R D C attachment_inverse_at attachment_inverse_commutes.
Theorem attachment_relative_quasi_isomorphism : quasi_isomorphism attachment_relative_map.
Proof.
apply: degreewise_bijective_quasi_isomorphism.
- exact: attachment_relative_injective.
- move=> k x; exists (attachment_inverse_at k x); exact: attachment_relative_inverseK.
Qed.
End Attachment.
End DPSimplicialAttachmentRelativeChains.
