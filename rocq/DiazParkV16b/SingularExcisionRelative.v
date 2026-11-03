(** Relative excision for the literal inclusion of an actual two-open cover. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleMaps MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainSubcomplex
  ChainSubcomplexMaps ChainMapImage ChainDegreewiseIso ChainSubcomplexComparison ChainHomologySquares
  SingularCohomology SingularSmallChains SmallSingularChainComparison
  SingularChainExcisionSubspaces SingularChainExcisionSubspacesLattice
  SingularExcisionSmallMaps SingularExcisionQuotientAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainSubcomplex DPChainSubcomplexMaps DPChainMapImage DPChainDegreewiseIso DPChainSubcomplexComparison
  DPChainHomologySquares DPSingularCohomology DPSingularSmallChains DPSmallSingularChainComparison
  DPSingularChainExcisionSubspaces DPSingularChainExcisionSubspacesLattice
  DPSingularExcisionSmallMaps DPSingularExcisionQuotientAlgebra.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularExcisionRelative.
Section RelativeExcision.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variables A B : set X.
Let CI := singular_chains Real R (subset_space (A `&` B)).
Let CA := singular_chains Real R (subset_space A).
Let CB := singular_chains Real R (subset_space B).
Let CS := @small_chains Real X bool (binary_cover A B) R.
Let CX := singular_chains Real R X.
Let f := intersection_to_left Real R A B.
Let j := intersection_to_right Real R A B.
Let k := small_left Real R A B.
Let l := small_right Real R A B.
Let inc := @small_chain_inclusion Real X bool (binary_cover A B) R.
Let incA := subspace_chain_inclusion Real A R.
Let incB := subspace_chain_inclusion Real B R.

Definition small_relative_excision_map : chain_map (relative_chain f) (relative_chain l) :=
  quotient_union_map (@small_intersection_square Real R X A B).

Definition small_relative_excision_homology_iso n : @isomorphism (module_category R)
 (homology (relative_chain f) n) (homology (relative_chain l) n) :=
  quotient_union_homology_iso (@small_intersection_square Real R X A B)
    (@small_sum_kernel Real R X A B) (@small_sum_surjective Real R X A B) n.

Definition small_relative_preserves n x : subspace_at (image_subcomplex l) n x ->
    subspace_at (image_subcomplex incB) n (chain_map_at inc n x).
Proof.
move=> [b <-]; exists b; symmetry; exact: small_right_ambient.
Defined.
Definition small_relative_subcomplex_map :=
  @subcomplex_map R CS CX inc (image_subcomplex l) (image_subcomplex incB) small_relative_preserves.
Definition small_relative_ambient_map :=
  @relative_map R CS CX inc (image_subcomplex l) (image_subcomplex incB) small_relative_preserves.

Lemma small_relative_subcomplex_injective n : injective (chain_map_at small_relative_subcomplex_map n).
Proof.
move=> a b h; apply submodule_val_injective.
apply: (@small_chain_inclusion_injective Real X bool (binary_cover A B) R n).
exact (congr1 (fun q => (val q : chain_term CX n)) h).
Qed.

Lemma small_relative_subcomplex_surjective n q : exists x,
  chain_map_at small_relative_subcomplex_map n x = q.
Proof.
case: (submodule_val_mem q) => b hb.
exists (chain_map_at (image_factor l) n b); apply submodule_val_injective.
change (chain_map_at inc n (chain_map_at l n b) = val q).
by rewrite small_right_ambient.
Qed.

Definition relative_excision_preserves n x : subspace_at (image_subcomplex f) n x ->
    subspace_at (image_subcomplex incB) n (chain_map_at incA n x).
Proof.
move=> [c <-]; exists (chain_map_at j n c).
rewrite -(@small_right_ambient Real R X A B n (chain_map_at j n c)).
rewrite -(@small_intersection_square Real R X A B n c) small_left_ambient.
reflexivity.
Defined.

Definition relative_excision_map : chain_map (relative_chain f) (relative_chain incB) :=
  @relative_map R CA CX incA (image_subcomplex f) (image_subcomplex incB) relative_excision_preserves.

Theorem relative_excision_map_projection n a :
  chain_map_at relative_excision_map n (chain_map_at (relative_projection f) n a) =
  chain_map_at (relative_projection incB) n (chain_map_at incA n a).
Proof. exact: relative_map_projection. Qed.

Lemma relative_excision_factor n q :
  chain_map_at small_relative_ambient_map n (chain_map_at small_relative_excision_map n q) =
  chain_map_at relative_excision_map n q.
Proof.
case: (@relative_projection_surjective R CI CA f n q) => a <-.
rewrite relative_excision_map_projection.
change (chain_map_at small_relative_ambient_map n
 (chain_map_at (quotient_union_map (@small_intersection_square Real R X A B)) n
 (chain_map_at (relative_projection f) n a)) =
 chain_map_at (relative_projection incB) n (chain_map_at incA n a)).
rewrite (@quotient_union_projection R CI CA CB CS f j k l
  (@small_intersection_square Real R X A B) n a).
rewrite relative_map_projection small_left_ambient.
reflexivity.
Qed.

Variable hA : open A.
Variable hB : open B.
Variable hcover : forall x, A x \/ B x.

Let smallIso n := @small_singular_homology_iso Real R X bool (binary_cover A B)
  (@binary_cover_open X A B hA hB) (@binary_cover_covers X A B hcover) n.
Let subIso n := degreewise_homology_iso (@small_relative_subcomplex_injective)
  (@small_relative_subcomplex_surjective) n.

Definition small_relative_ambient_homology_iso n : @isomorphism (module_category R)
 (homology (relative_chain l) n) (homology (relative_chain incB) n) :=
  @relative_homology_iso R CS CX inc (image_subcomplex l) (image_subcomplex incB) small_relative_preserves
    (fun n => @module_iso_hom_injective R _ _ (subIso n))
    (fun n q => ex_intro _ (module_hom_fun (iso_inv (subIso n)) q) (module_iso_inv_hom_apply (subIso n) q))
    (fun n => @module_iso_hom_injective R _ _ (smallIso n))
    (fun n q => ex_intro _ (module_hom_fun (iso_inv (smallIso n)) q) (module_iso_inv_hom_apply (smallIso n) q)) n.

Definition relative_excision_homology_iso n : @isomorphism (module_category R)
 (homology (relative_chain f) n) (homology (relative_chain incB) n) :=
  module_iso_comp (small_relative_excision_homology_iso n) (small_relative_ambient_homology_iso n).

Theorem relative_excision_homology_iso_hom n q :
  module_hom_fun (iso_hom (relative_excision_homology_iso n)) q = homology_map relative_excision_map n q.
Proof.
change (module_hom_fun (iso_hom (small_relative_ambient_homology_iso n))
  (homology_map small_relative_excision_map n q) =
  homology_map relative_excision_map n q).
rewrite /small_relative_ambient_homology_iso relative_homology_iso_hom.
case: (quotient_pi_surjective q) => z <-; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
exact: relative_excision_factor.
Qed.

End RelativeExcision.
End DPSingularExcisionRelative.
