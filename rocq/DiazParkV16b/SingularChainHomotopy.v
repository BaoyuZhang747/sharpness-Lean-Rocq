(** Actual singular chain homotopy and quotient-homology invariance. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  SingularSet SingularCohomology TopologicalCategory TopologicalCategoryHomotopy
  SingularHomotopyPrismIndexed SimplicialPrismChainHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPSingularSet DPSingularCohomology
  DPSingularPrismIndexed DPSimplicialPrismChainHomotopy
  DPChainComplex DPChainHomology DPChainHomologyMaps.

Module DPSingularChainHomotopy.
Section Invariance.
Variable Real : realType.
Variable R : pzRingType.
Variables X Y : topologicalType.
Variables f g : hom topological_category X Y.
Variable H : continuous_homotopy Real f g.

Definition singular_chain_homotopy :
    chain_homotopy (singular_chain_map Real R g) (singular_chain_map Real R f) :=
  @simplicial_prism_chain_homotopy R (singular_set Real X) (singular_set Real Y)
    (singular_map Real f) (singular_map Real g)
    (@singular_indexed_prism Real X Y f g H)
    (@singular_indexed_prism_first Real X Y f g H)
    (@singular_indexed_prism_last Real X Y f g H)
    (@singular_indexed_prism_middle Real X Y f g H)
    (@singular_indexed_prism_left Real X Y f g H)
    (@singular_indexed_prism_right Real X Y f g H).

Theorem singular_homology_homotopy n (q : homology (singular_chains Real R X) n) :
  homology_map (singular_chain_map Real R g) n q =
    homology_map (singular_chain_map Real R f) n q.
Proof. exact: (homology_map_homotopy singular_chain_homotopy q). Qed.

Theorem singular_homology_homotopy_functions n :
  (fun q => homology_map (singular_chain_map Real R g) n q) =
    (fun q => homology_map (singular_chain_map Real R f) n q).
Proof. apply functional_extensionality_dep; exact: singular_homology_homotopy. Qed.

End Invariance.
Arguments singular_chain_homotopy {Real} R {X Y f g} H.
Arguments singular_homology_homotopy {Real R X Y f g} H {n} q.
End DPSingularChainHomotopy.
