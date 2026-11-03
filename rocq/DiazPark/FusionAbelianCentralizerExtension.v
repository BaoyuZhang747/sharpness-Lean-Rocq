From mathcomp Require Import all_ssreflect all_fingroup center abelian.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionReceptivity.
Import DPFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAbelianCentralizerExtension.
Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variables A B : {group S}.
Variable f : DPFusion.map A B.
Hypothesis hf : DPFusionSystem.allowed F f.
Hypothesis onto : DPFusion.image f = B.
Hypothesis abA : abelian A.
Hypothesis hB : DPFusionSystem.fully_centralized F B.

Theorem centralizer_extension_exists :
  exists g : DPFusion.map 'C(A)%G 'C(B)%G,
    DPFusionSystem.allowed F g /\ {in A, g =1 f}.
Proof.
have [h [hh he]] := DPFusionSaturation.saturation_extension sat hf onto hB.
pose g := DPFusionReceptivity.centralizer_extension onto he.
exists g; split.
- apply: DPFusionSystem.corestriction_allowed.
  exact: DPFusionSystem.restriction_allowed hh.
- move=> x Ax; rewrite /g DPFusionReceptivity.centralizer_extensionE.
  + exact: he Ax.
  + exact: subsetP abA x Ax.
Qed.
End Extension.
End DPFusionAbelianCentralizerExtension.

