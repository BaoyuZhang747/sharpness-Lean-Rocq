(** Stable elements of actual ordinary cohomology, expressed by literal
    subgroup restriction and ambient conjugation maps. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules MackeyModuleCarriers.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyInner GroupCohomologyOrbitCoefficient
  GroupCohomologyHomogeneousRestriction GroupCohomologyHomogeneousConjugation
  GroupCohomologyTransferCosets GroupCohomologyTransferNative GroupCohomologyTransferIndex
  GroupCohomologyTransferDoubleCoset GroupCohomologyCosetSumsDoubleCosets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor
  DPGroupCohomologyPullback DPGroupCohomologyInner
  DPGroupCohomologyHomogeneousRestriction DPGroupCohomologyHomogeneousConjugation
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferIndex
  DPGroupCohomologyTransferDoubleCoset DPGroupCohomologyCosetSumsDoubleCosets.
Local Open Scope ring_scope.

Module DPGroupCohomologyStableElementsBase.
Section Stable.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q : {group G}.
Variable hPQ : P \subset Q.
Variable A : lmodType R.
Variable n : nat.

Definition stable (z : value R [the finGroupType of [subg P]] A n) : Prop :=
  forall (L : {group G}) (hLP : L \subset P) (x : G), x \in Q ->
    forall hLx : L \subset (P :^ x)%g,
      module_hom_fun (pull A (@subgroup_conjugation_hom G L P x hLx) n) z =
      module_hom_fun (pull A (subgroup_nested_hom hLP) n) z.

Lemma conjugation_inclusion_square (L : {group G}) (hLP : L \subset P)
    (x : G) (hx : x \in Q) (hLx : L \subset (P :^ x)%g) :
  group_hom_comp (@subgroup_conjugation_hom G L P x hLx)
      (subgroup_nested_hom hPQ) =
  group_hom_comp (subgroup_nested_hom (subset_trans hLP hPQ))
      (group_conjugation ((subg Q x)^-1)%g).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => a.
apply val_inj.
change (val (subgroup_nested_hom hPQ
    (@subgroup_conjugation_hom G L P x hLx a)) =
  val ((subgroup_nested_hom (subset_trans hLP hPQ) a) ^ (subg Q x)^-1)%g).
rewrite !subgroup_nested_hom_val subgroup_conjugation_hom_val.
change ((val a ^ x^-1)%g =
  (val (subgroup_nested_hom (subset_trans hLP hPQ) a) ^ (val (subg Q x))^-1)%g).
by rewrite subgroup_nested_hom_val subgK.
Qed.

Lemma nested_composition (L : {group G}) (hLP : L \subset P) :
  group_hom_comp (subgroup_nested_hom hLP) (subgroup_nested_hom hPQ) =
    subgroup_nested_hom (subset_trans hLP hPQ).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => a.
apply val_inj.
change (val (subgroup_nested_hom hPQ (subgroup_nested_hom hLP a)) =
  val (subgroup_nested_hom (subset_trans hLP hPQ) a)).
by rewrite !subgroup_nested_hom_val.
Qed.

Theorem restriction_stable (z : value R [the finGroupType of [subg Q]] A n) :
  stable (module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z).
Proof.
move=> L hLP x hx hLx.
have hc := congr1 (fun f => module_hom_fun f z)
  (@pull_composition R A _ _ _ (@subgroup_conjugation_hom G L P x hLx)
    (subgroup_nested_hom hPQ) n).
change (module_hom_fun (pull A (group_hom_comp
  (@subgroup_conjugation_hom G L P x hLx) (subgroup_nested_hom hPQ)) n) z =
  module_hom_fun (pull A (@subgroup_conjugation_hom G L P x hLx) n)
    (module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z)) in hc.
rewrite -hc conjugation_inclusion_square // pull_composition pull_inner.
change (module_hom_fun (pull A (subgroup_nested_hom (subset_trans hLP hPQ)) n) z =
  module_hom_fun (pull A (subgroup_nested_hom hLP) n)
    (module_hom_fun (pull A (subgroup_nested_hom hPQ) n) z)).
by rewrite -nested_composition pull_composition.
Qed.

Theorem restriction_transfer_stable_index
    (z : value R [the finGroupType of [subg P]] A n) (hz : stable z) :
  module_hom_fun (pull A (subgroup_nested_hom hPQ) n)
    (module_hom_fun (transfer A hPQ n) z) = z *+ indexg Q P.
Proof.
rewrite (@transfer_double_coset R G P P Q hPQ hPQ A n z).
transitivity (\sum_(D in double_cosets P P Q)
  z *+ indexg P (@intersection G P P (double_coset_repr P D))).
- apply: eq_bigr => D hD.
  change (module_hom_fun (transfer A (@intersection_sub_Q G P P _) n)
    (module_hom_fun (pull A (@subgroup_conjugation_hom G
      (@intersection G P P (double_coset_repr P D)) P (double_coset_repr P D)
      (@intersection_sub_conjugate G P P _)) n) z) =
    z *+ indexg P (@intersection G P P (double_coset_repr P D))).
  rewrite (hz _ (@intersection_sub_Q G P P _) _
    (@double_coset_repr_mem G P P Q hPQ hPQ D hD)) transfer_restriction_index.
  reflexivity.
- have hc := @coset_sum_double_coset G P P Q hPQ
    (value R [the finGroupType of [subg P]] A n)
    (fun _ => z) (fun _ _ _ => Logic.eq_refl z).
  rewrite /DPGroupCohomologyTransferCosets.coset_sum sumr_const in hc.
  rewrite hc; apply: eq_bigr => D hD; by rewrite sumr_const.
Qed.

End Stable.
End DPGroupCohomologyStableElementsBase.
