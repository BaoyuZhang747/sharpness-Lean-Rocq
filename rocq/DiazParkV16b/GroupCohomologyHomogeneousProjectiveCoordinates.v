(** Explicit free H-orbits of G^(n+1), using right cosets Hx and normalized
    tail coordinates. No projectivity or orbit decomposition is assumed. *)
From mathcomp Require Import all_ssreflect all_fingroup.
From DiazParkV16b Require Import GroupCohomologyHomogeneousPaths.
Import DPGroupCohomologyHomogeneousPaths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPGroupCohomologyHomogeneousProjectiveCoordinates.
Section Coordinates.
Variable G : finGroupType.
Variable H : {group G}.
Local Notation HS := [subg H]%type.

Definition representative_type := {r : G | repr (H :* r) == r}.

Lemma representative_fixed x : repr (H :* repr (H :* x)) == repr (H :* x).
Proof. by rewrite rcoset_repr. Qed.

Definition representative (x : G) : representative_type :=
  exist (fun r : G => is_true (repr (H :* r) == r))
    (repr (H :* x)) (representative_fixed x).

Lemma representative_left h x : h \in H -> representative (h * x) = representative x.
Proof.
move=> Hh; apply: val_inj; change (repr (H :* (h * x)) = repr (H :* x)).
congr (repr _); apply/rcoset_eqP/rcosetP; by exists h.
Qed.

Lemma representative_self (r : representative_type) : representative (val r) = r.
Proof. apply: val_inj; exact: eqP (valP r). Qed.

Lemma coefficient_mem x : x * (val (representative x))^-1 \in H.
Proof.
change (x * (repr (H :* x))^-1 \in H).
by rewrite -mem_rcoset rcoset_sym mem_repr_rcoset.
Qed.

Definition coefficient (x : G) : HS := subg H (x * (val (representative x))^-1).

Lemma coefficientE x : val (coefficient x) = x * (val (representative x))^-1.
Proof. exact: subgK (coefficient_mem x). Qed.

Lemma reassemble x : val (coefficient x) * val (representative x) = x.
Proof. by rewrite coefficientE mulgKV. Qed.

Lemma coefficient_representative (a : HS) (r : representative_type) :
  coefficient (val a * val r) = a.
Proof.
apply: val_inj; by rewrite coefficientE representative_left ?subgP // representative_self mulgK.
Qed.

Definition orbit_index n := (representative_type * power G n)%type.
Definition orbit_generator n := (orbit_index n * HS)%type.

Definition expand n (a : orbit_generator n) : homogeneous_generator G n :=
  (val a.2 * val a.1.1, left_translate n (val a.2 * val a.1.1) a.1.2).

Definition coordinates n (v : homogeneous_generator G n) : orbit_generator n :=
  ((representative v.1, left_translate n v.1^-1 v.2), coefficient v.1).

Lemma expand_coordinates n (v : homogeneous_generator G n) :
  expand (coordinates v) = v.
Proof.
case: v=> x v; rewrite /coordinates /expand /= reassemble.
by rewrite -left_translate_composition mulgV left_translate_identity.
Qed.

Lemma coordinates_expand n (a : orbit_generator n) : coordinates (expand a) = a.
Proof.
case: a=> [[r v] h]; rewrite /coordinates /expand /=.
rewrite representative_left ?subgP // representative_self coefficient_representative.
by rewrite -left_translate_composition mulVg left_translate_identity.
Qed.

Definition regular_translate n (a : HS) (v : orbit_generator n) : orbit_generator n :=
  (v.1, a * v.2).

Lemma expand_translate n (a : HS) (v : orbit_generator n) :
  expand (regular_translate a v) = left_translate n.+1 (val a) (expand v).
Proof.
case: v=> [[r v] h]; rewrite /regular_translate /expand /=.
change (((val a * val h) * val r, left_translate n ((val a * val h) * val r) v) =
  (val a * (val h * val r), left_translate n (val a) (left_translate n (val h * val r) v))).
by rewrite -left_translate_composition mulgA.
Qed.

End Coordinates.
End DPGroupCohomologyHomogeneousProjectiveCoordinates.

Print Assumptions DPGroupCohomologyHomogeneousProjectiveCoordinates.expand_coordinates.
Print Assumptions DPGroupCohomologyHomogeneousProjectiveCoordinates.coordinates_expand.
Print Assumptions DPGroupCohomologyHomogeneousProjectiveCoordinates.expand_translate.
