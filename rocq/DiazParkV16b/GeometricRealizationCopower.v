(** Actual realization of a simplicial copower as a topological disjoint family. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology sigT_topology unstable.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialCopower
  TopologicalCategory TopologicalSimplexBasic TopologicalSimplexAffine TopologicalCoproductHomotopy
  GeometricRealizationCarrier GeometricRealizationUniversal GeometricRealizationMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPSimplicialCopower DPTopological DPTopologicalCoproductHomotopy
  DPGeometricRealization DPGeometricRealizationUniversal DPGeometricRealizationMaps.

Module DPGeometricRealizationCopower.
Section Copower.
Variable Real : realType.
Variable I : Type.
Variable X : simplicial_set.
Definition copower_realization_family : topologicalType :=
  @family_space [the choiceType of {classic I}] (fun _ => realization_space Real X).

Definition copower_forward_family : simplex_family Real (copower I X) copower_realization_family :=
  fun n z t => existT (fun _ : [the choiceType of {classic I}] => realization_space Real X)
    z.1 (@characteristic Real X n z.2 t).

Lemma copower_forward_compatible : family_compatible copower_forward_family.
Proof.
move=> n m a [i x] t.
change (existT _ i (@characteristic Real X n (simplex_map X a x) t) =
  existT _ i (@characteristic Real X m x (DPTopologicalSimplexAffine.pushforward a t))).
by rewrite characteristic_ordinal.
Qed.

Lemma copower_forward_family_continuous n (z : simplex (copower I X) n) :
  continuous (copower_forward_family z : DPTopologicalSimplex.simplex_space Real n -> copower_realization_family).
Proof.
case: z => i x; move=> t.
apply: (@continuous_comp (DPTopologicalSimplex.simplex_space Real n) (realization_space Real X)
  copower_realization_family (@characteristic Real X n x)
  (existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i) t);
  [exact: characteristic_continuous | exact: existT_continuous].
Qed.

Definition copower_forward : continuousType (realization_space Real (copower I X)) copower_realization_family :=
  @descent_map Real (copower I X) copower_realization_family copower_forward_family
    copower_forward_compatible (@copower_forward_family_continuous).

Lemma copower_forward_characteristic n i (x : simplex X n) t :
  copower_forward (@characteristic Real (copower I X) n (i,x) t) =
    existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i (@characteristic Real X n x t).
Proof.
exact (@descent_characteristic Real (copower I X) copower_realization_family
  copower_forward_family copower_forward_compatible n (i,x) t).
Qed.

Definition copower_inverse (z : copower_realization_family) : realization_space Real (copower I X) :=
  realization_map Real (@copower_inclusion I X (projT1 z)) (projT2 z).

Lemma copower_inverse_continuous : continuous copower_inverse.
Proof.
apply: (@sigT_continuous [the choiceType of {classic I}] (fun _ => realization_space Real X)
  (realization_space Real (copower I X))
  (fun i z => realization_map Real (@copower_inclusion I X i) z)).
move=> i; exact: cts_fun.
Qed.

Lemma copower_forwardK : cancel copower_forward copower_inverse.
Proof.
move=> z; have [[[n [i x]] t] <-] := realization_class_surjective z.
change (copower_inverse (copower_forward (@characteristic Real (copower I X) n (i,x) t)) =
  @characteristic Real (copower I X) n (i,x) t).
rewrite copower_forward_characteristic /copower_inverse /= realization_map_characteristic; reflexivity.
Qed.
Lemma copower_inverseK : cancel copower_inverse copower_forward.
Proof.
move=> [i z]; have [[[n x] t] <-] := realization_class_surjective z.
change (copower_forward (realization_map Real (@copower_inclusion I X i) (@characteristic Real X n x t)) =
  existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i (@characteristic Real X n x t)).
rewrite realization_map_characteristic; exact: copower_forward_characteristic.
Qed.

Definition realization_copower_homeomorphism : homeomorphism
    (realization_space Real (copower I X)) copower_realization_family :=
  homeomorphism_of_inverse (@cts_fun _ _ copower_forward) copower_inverse_continuous
    copower_forwardK copower_inverseK.

Theorem realization_copower_homeomorphism_characteristic n i (x : simplex X n) t :
  iso_hom realization_copower_homeomorphism (@characteristic Real (copower I X) n (i,x) t) =
    existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i (@characteristic Real X n x t).
Proof. exact: copower_forward_characteristic. Qed.

Theorem realization_copower_homeomorphism_inverse i z :
  iso_inv realization_copower_homeomorphism
    (existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i z) =
  realization_map Real (@copower_inclusion I X i) z.
Proof. reflexivity. Qed.

End Copower.
End DPGeometricRealizationCopower.
