From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy FusionAutomorphisms
  FusionSaturationImage.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinWords.
Section Words.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Record generator := Generator {
  generator_group : {group S};
  generator_centric : DPFusionSystem.centric F generator_group;
  generator_map : DPFusion.map generator_group generator_group;
  generator_allowed : DPFusionSystem.allowed F generator_map
}.

(** A step is onto its named target, so its target is its exact image. *)
Record restriction (a : generator) (P Q : {group S}) := Restriction {
  step_map : DPFusion.map P Q;
  step_onto : DPFusion.image step_map = Q;
  step_source : P \subset generator_group a;
  step_target : Q \subset generator_group a;
  step_agrees : {in P, step_map =1 generator_map a}
}.

Lemma step_allowed (a : generator) (P Q : {group S}) (r : restriction a P Q) :
  DPFusionSystem.allowed F (step_map r).
Proof.
have h := DPFusionSystem.restriction_allowed (step_source r) (generator_allowed a).
have him : DPFusion.image (DPFusion.restrict (generator_map a) (step_source r)) \subset Q.
  apply/subsetP=> y /morphimP[x Px _ ->].
  rewrite DPFusion.map_morphismE DPFusion.restrict_in // -(step_agrees r Px).
  exact: DPFusion.map_into Px.
have e : DPFusion.corestrict him = step_map r.
  apply: DPFusion.map_ext=> x Px.
  by rewrite DPFusion.corestrict_in // DPFusion.restrict_in // (step_agrees r Px).
rewrite -e; exact: DPFusionSystem.corestriction_allowed him h.
Qed.

Inductive word : {group S} -> {group S} -> seq generator -> Type :=
| word_nil P : word P P [::]
| word_cons P Q R (a : generator) (r : restriction a P Q) l
    (w : word Q R l) : word P R (a :: l).

Fixpoint evaluation P Q l (w : word P Q l) : DPFusion.map P Q :=
  match w in word A B _ return DPFusion.map A B with
  | word_nil A => DPFusion.identity A
  | @word_cons A B C a r l t => DPFusion.compose (step_map r) (evaluation t)
  end.

Fixpoint append P Q l (w : word P Q l) :
    forall R m, word Q R m -> word P R (l ++ m) :=
  match w in word A B l0 return forall R m, word B R m -> word A R (l0 ++ m) with
  | word_nil A => fun R m v => v
  | @word_cons A B C a r l0 t => fun R m v => word_cons r (append t v)
  end.

Lemma evaluation_nil P : evaluation (word_nil P) = DPFusion.identity P.
Proof. by []. Qed.

Lemma evaluation_append P Q l (w : word P Q l) R m (v : word Q R m) :
  evaluation (append w v) = DPFusion.compose (evaluation w) (evaluation v).
Proof.
elim: w=> [A|A B C a r l0 t ih] in R m v *; simpl.
- by rewrite DPFusion.identity_compose.
- by rewrite ih DPFusion.compose_assoc.
Qed.

Lemma evaluation_allowed P Q l (w : word P Q l) :
  DPFusionSystem.allowed F (evaluation w).
Proof.
elim: w=> [A|A B C a r l0 t ih]; simpl.
- exact: DPFusionSystem.identity_allowed.
- exact: DPFusionSystem.composition_closed (step_allowed r) ih.
Qed.

Lemma evaluation_onto P Q l (w : word P Q l) : DPFusion.image (evaluation w) = Q.
Proof.
elim: w=> [A|A B C a r l0 t ih]; simpl.
- exact: DPFusionConjugacy.identity_image.
- exact: DPFusionConjugacy.compose_onto (step_onto r) ih.
Qed.

Definition factorizable P Q (f : DPFusion.map P Q) : Prop :=
  exists l, exists w : word P Q l, evaluation w = f.

Lemma factorizable_identity P : factorizable (DPFusion.identity P).
Proof. by exists [::], (word_nil P). Qed.

Lemma factorizable_compose P Q R (f : DPFusion.map P Q) (g : DPFusion.map Q R) :
  factorizable f -> factorizable g -> factorizable (DPFusion.compose f g).
Proof.
move=> [l [w <-]] [m [v <-]].
exists (l ++ m), (append w v); exact: evaluation_append.
Qed.

(** The induction predicate includes every isomorphic restriction of f. *)
Definition strongly_factorizable P Q (f : DPFusion.map P Q) : Prop :=
  forall (A B : {group S}) (d : DPFusion.map A B),
    A \subset P -> B \subset Q -> DPFusion.image d = B ->
    {in A, d =1 f} -> factorizable d.

Lemma strongly_factorizable_restrict P Q (f : DPFusion.map P Q) A B
    (d : DPFusion.map A B) :
  strongly_factorizable f -> A \subset P -> B \subset Q ->
  {in A, d =1 f} -> strongly_factorizable d.
Proof.
move=> hf sAP sBQ he C D k sCA sDB onto hk.
apply: (hf C D k (subset_trans sCA sAP) (subset_trans sDB sBQ) onto).
move=> x Cx; rewrite hk //; exact: he _ (subsetP sCA x Cx).
Qed.

Lemma strongly_factorizable_centric P (a : DPFusion.map P P) :
  DPFusionSystem.centric F P -> DPFusionSystem.allowed F a -> strongly_factorizable a.
Proof.
move=> hP ha A B d sAP sBP onto hd.
pose gen := Generator hP ha.
pose r : restriction gen A B := @Restriction gen A B d onto sAP sBP hd.
exists [:: gen], (word_cons r (word_nil B)).
exact: DPFusion.compose_identity.
Qed.

End Words.
End DPFusionAlperinWords.


