(** Exact normalizer action squares for actual linking restrictions. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemAutomorphisms LinkingSystemCancellation NormalizerChainTransporter.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms
  DPLinkingCancellation DPNormalizerChainTransporter.
Local Open Scope group_scope.

Module DPLinkingNormalizerSquares.
Section Squares.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma normalizer_inclusion_square (P Q : Obj) (hPQ : val P \subset val Q)
    (x : [subg (val Q)]) (hx : val x \in 'N(val P)) :
  linking_compose L (normalizer_map L (Sub (val x) hx)) (inclusion L hPQ) =
    linking_compose L (inclusion L hPQ) (distinguished L x).
Proof.
rewrite /normalizer_map /inclusion /distinguished -!transporter_compose.
congr (linking_transporter L _); apply val_inj.
change (val x * 1 = 1 * val x); by rewrite mulg1 mul1g.
Qed.

Variables U N T : Obj.
Hypothesis hUN : val U \subset val N.
Hypothesis hUT : val U \subset val T.
Hypothesis hNN : val N \subset 'N(val U).
Hypothesis hTN : val T \subset 'N(val U).
Variable a : automorphism_group L U.
Variable b : linking_hom L N T.
Hypothesis square : linking_compose L a (inclusion L hUT) =
  linking_compose L (inclusion L hUN) b.

Definition source_normalizer (x : [subg (val N)]) : [subg 'N(val U)] :=
  Sub (val x) (subsetP hNN _ (valP x)).

Definition target_normalizer (x : [subg (val N)]) : [subg 'N(val U)] :=
  Sub (val (arrow_element (linking_projection L b) x))
    (subsetP hTN _ (valP (arrow_element (linking_projection L b) x))).

Theorem extension_intertwines (x : [subg (val N)]) :
  normalizer_map L (source_normalizer x) * a =
    a * normalizer_map L (target_normalizer x).
Proof.
apply (@compose_right_injective S F L U U T (inclusion L hUT)).
rewrite !automorphism_mul !linking_assoc square -linking_assoc.
rewrite normalizer_inclusion_square linking_assoc (@commutation S F L N T b x).
rewrite -linking_assoc -square linking_assoc.
rewrite -(@normalizer_inclusion_square U T hUT
  (arrow_element (linking_projection L b) x)
  (subsetP hTN _ (valP (arrow_element (linking_projection L b) x)))).
reflexivity.
Qed.

Theorem extension_conjugation (x : [subg (val N)]) :
  normalizer_map L (target_normalizer x) = normalizer_map L (source_normalizer x) ^ a.
Proof.
have he := extension_intertwines x.
have hm := congr1 (fun z : automorphism_group L U => a^-1 * z) he.
rewrite !mulgA mulVg mul1g in hm.
rewrite /conjg mulgA.
exact (esym hm).
Qed.
End Squares.
End DPLinkingNormalizerSquares.

Check DPLinkingNormalizerSquares.extension_conjugation.
Print Assumptions DPLinkingNormalizerSquares.normalizer_inclusion_square.
Print Assumptions DPLinkingNormalizerSquares.extension_conjugation.
