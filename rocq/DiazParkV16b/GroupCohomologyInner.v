(** Inner conjugation acts trivially on the actual ordinary group cohomology,
    by the constructed constant-coefficient bar prism. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback CategoryBarPullbackConstant CategoryBarPullbackHomotopy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DiazParkHomological DiazParkCohomologyMaps DPCategoryBarConstant DPCategoryBarHomotopy.

Module DPGroupCohomologyInner.
Section Inner.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable A : lmodType R.
Variable a : G.

Definition inner_cochain_homotopy :
    cochain_homotopy (pull_cochain A (group_conjugation a))
      (pull_cochain A (group_hom_identity G)).
Proof.
unfold pull_cochain; rewrite group_functor_identity.
exact (constant_bar_nat_trans_homotopy A (inner_nat_trans a)).
Defined.

Theorem pull_inner n :
  pull A (group_conjugation a) n = module_hom_id (value R G A n).
Proof.
rewrite -(@pull_identity R A G n).
apply module_hom_ext => q.
exact: (cohomology_map_homotopy inner_cochain_homotopy q).
Qed.

End Inner.
End DPGroupCohomologyInner.
