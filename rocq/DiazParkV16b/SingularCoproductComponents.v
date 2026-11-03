(** The actual singular simplicial set preserves arbitrary copowers of spaces. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology sigT_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialCopower
  TopologicalCategory TopologicalSimplexBasic TopologicalSimplexConnected
  TopologicalCoproductHomotopy TopologicalConnectedCoproduct SingularSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPSimplicialCopower DPTopological
  DPTopologicalSimplexConnected DPTopologicalCoproductHomotopy
  DPTopologicalConnectedCoproduct DPSingularSet.

Module DPSingularCoproductComponents.
Section Copower.
Variable Real : realType.
Variable I : Type.
Variable X : topologicalType.

Definition space_copower : topologicalType :=
  @family_space [the choiceType of {classic I}] (fun _ => X).
Definition space_copower_inclusion (i : I) : continuousType X space_copower :=
  continuous_map (@existT_continuous [the choiceType of {classic I}] (fun _ => X) i).

Definition singular_copower_map : simplicial_map
    (copower I (singular_set Real X)) (singular_set Real space_copower) :=
  copower_desc (fun i => singular_map Real (space_copower_inclusion i)).

Lemma singular_copower_map_at n i (s : simplex (singular_set Real X) n) t :
  component singular_copower_map n (i,s) t = existT (fun _ : [the choiceType of {classic I}] => X) i (s t).
Proof. reflexivity. Qed.

Lemma singular_copower_map_injective n : injective (component singular_copower_map n).
Proof.
move=> [i s] [j t] h.
have ei : i = j := congr1 (fun a : simplex (singular_set Real space_copower) n =>
  projT1 (a (@DPTopologicalSimplex.vertex Real n ord0))) h.
subst j; congr (i,_); apply/continuousEP => x.
apply: (@existT_inj2 [the eqType of {classic I}] (fun _ => X) i).
exact (congr1 (fun a : simplex (singular_set Real space_copower) n => a x) h).
Qed.

Lemma singular_copower_map_surjective n (s : simplex (singular_set Real space_copower) n) :
  exists a, component singular_copower_map n a = s.
Proof.
pose z0 := @DPTopologicalSimplex.vertex Real n ord0.
pose i := @connected_family_index [the choiceType of {classic I}] (fun _ => X)
  (DPTopologicalSimplex.simplex_space Real n) z0 s.
pose f := @connected_family_factor [the choiceType of {classic I}] (fun _ => X)
  (DPTopologicalSimplex.simplex_space Real n) z0 (@simplex_connected Real n) s.
exists (i,f); apply/continuousEP => x.
exact: connected_family_factor_equation.
Qed.

End Copower.
End DPSingularCoproductComponents.
