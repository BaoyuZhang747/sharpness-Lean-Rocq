(** Exactness of free modules on an intersection and a binary union of actual subsets. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import BarFreeModule.
From DiazParkV16b Require Import FreeModuleEmbeddings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPFreeModuleEmbeddings.
Local Open Scope ring_scope.

Module DPFreeModuleBinaryUnion.
Section Binary.
Variable R : pzRingType.
Variable X : Type.
Variables P Q : X -> Prop.
Lemma binary_subset_ext (S : X -> Prop) (x y : {z : X | S z}) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
case: x => x hx; case: y => y hy /= e; subst y; f_equal; apply Prop_irrelevance.
Qed.
Definition left_set := {x : X | P x}.
Definition right_set := {x : X | Q x}.
Definition inter_set := {x : X | P x /\ Q x}.
Definition union_set := {x : X | P x \/ Q x}.
Definition inter_left_fun (x : inter_set) : left_set := exist _ (proj1_sig x) (proj1 (proj2_sig x)).
Definition inter_right_fun (x : inter_set) : right_set := exist _ (proj1_sig x) (proj2 (proj2_sig x)).
Definition union_left_fun (x : left_set) : union_set := exist _ (proj1_sig x) (or_introl (proj2_sig x)).
Definition union_right_fun (x : right_set) : union_set := exist _ (proj1_sig x) (or_intror (proj2_sig x)).
Definition inter_left := free_map R inter_left_fun.
Definition inter_right := free_map R inter_right_fun.
Definition union_left := free_map R union_left_fun.
Definition union_right := free_map R union_right_fun.

Lemma inter_left_injective : injective inter_left.
Proof.
apply: (@free_map_injective R inter_set left_set inter_left_fun).
move=> [x hx] [y hy] h.
have e : x = y := congr1 (@proj1_sig X P) h.
subst y; f_equal; apply Prop_irrelevance.
Qed.

Lemma intersection_square (a : free_module R inter_set) :
  union_left (inter_left a) = union_right (inter_right a).
Proof.
apply (free_lift_ext (g := (union_left \o inter_left : {linear _ -> _}))
  (h := (union_right \o inter_right : {linear _ -> _}))).
move=> x; rewrite /= /union_left /union_right /inter_left /inter_right !free_map_basis.
congr (free_basis R _); apply: binary_subset_ext; reflexivity.
Qed.

Definition left_basis (u : union_set) : free_module R left_set :=
  match pselect (P (proj1_sig u)) with
  | left h => free_basis R (exist _ (proj1_sig u) h)
  | right _ => 0
  end.
Definition right_proof (u : union_set) (h : ~ P (proj1_sig u)) : Q (proj1_sig u).
Proof. case: (proj2_sig u) => [hu|hu]; [exact: False_rect _ (h hu) | exact: hu]. Defined.
Definition right_basis (u : union_set) : free_module R right_set :=
  match pselect (P (proj1_sig u)) with
  | left _ => 0
  | right h => free_basis R (exist _ (proj1_sig u) (right_proof h))
  end.
Definition inter_basis (v : right_set) : free_module R inter_set :=
  match pselect (P (proj1_sig v)) with
  | left h => free_basis R (exist _ (proj1_sig v) (conj h (proj2_sig v)))
  | right _ => 0
  end.
Definition project_left : {linear free_module R union_set -> free_module R left_set} := free_lift left_basis.
Definition project_right : {linear free_module R union_set -> free_module R right_set} := free_lift right_basis.
Definition project_inter : {linear free_module R right_set -> free_module R inter_set} := free_lift inter_basis.
Lemma project_left_basis u : project_left (free_basis R u) = left_basis u.
Proof. exact: free_lift_basis. Qed.
Lemma project_right_basis u : project_right (free_basis R u) = right_basis u.
Proof. exact: free_lift_basis. Qed.
Lemma project_inter_basis v : project_inter (free_basis R v) = inter_basis v.
Proof. exact: free_lift_basis. Qed.

Definition zero_left_right (_ : free_module R left_set) : free_module R right_set := 0.
Lemma zero_left_right_linear : linear zero_left_right.
Proof. by move=> r a b; rewrite /zero_left_right scaler0 addr0. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ zero_left_right zero_left_right_linear.

Definition right_remainder (b : free_module R right_set) := b - inter_right (project_inter b).
Lemma right_remainder_linear : linear right_remainder.
Proof. by move=> r a b; rewrite /right_remainder !linearP scalerBr addrACA scalerN. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ right_remainder right_remainder_linear.

Definition union_reassembly (c : free_module R union_set) :=
  union_left (project_left c) + union_right (project_right c).
Lemma union_reassembly_linear : linear union_reassembly.
Proof. by move=> r a b; rewrite /union_reassembly !linearP scalerDr addrACA. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ union_reassembly union_reassembly_linear.

Lemma project_left_left (a : free_module R left_set) : project_left (union_left a) = a.
Proof.
apply (free_lift_ext (g := (project_left \o union_left : {linear _ -> _}))
  (h := (idfun : {linear free_module R left_set -> _}))).
move=> [x hx]; rewrite /= /union_left free_map_basis /project_left free_lift_basis /left_basis /=.
case: (pselect (P x)) => [h|h]; last exact: False_rect _ (h hx).
congr (free_basis R _); apply: binary_subset_ext; reflexivity.
Qed.

Lemma project_right_left (a : free_module R left_set) : project_right (union_left a) = 0.
Proof.
apply (free_lift_ext (g := (project_right \o union_left : {linear _ -> _}))
  (h := (zero_left_right : {linear free_module R left_set -> free_module R right_set}))).
move=> [x hx]; rewrite /= /union_left free_map_basis /project_right free_lift_basis /right_basis /=.
case: (pselect (P x)) => [h|h]; first reflexivity.
exact: False_rect _ (h hx).
Qed.

Lemma project_left_right (b : free_module R right_set) :
  project_left (union_right b) = inter_left (project_inter b).
Proof.
apply (free_lift_ext (g := (project_left \o union_right : {linear _ -> _}))
  (h := (inter_left \o project_inter : {linear _ -> _}))).
move=> [x hx]; rewrite /= /union_right free_map_basis /project_left /project_inter !free_lift_basis
  /left_basis /inter_basis /=.
case: (pselect (P x)) => [h|h]; last by rewrite linear0.
rewrite /inter_left free_map_basis; congr (free_basis R _).
apply: binary_subset_ext; reflexivity.
Qed.

Lemma project_right_right (b : free_module R right_set) :
  project_right (union_right b) = b - inter_right (project_inter b).
Proof.
apply (free_lift_ext (g := (project_right \o union_right : {linear _ -> _}))
  (h := (right_remainder : {linear _ -> _}))).
move=> [x hx].
change (project_right (union_right (free_basis R (exist Q x hx))) =
  free_basis R (exist Q x hx) - inter_right (project_inter (free_basis R (exist Q x hx)))).
rewrite /union_right free_map_basis project_right_basis project_inter_basis
  /right_basis /inter_basis /=.
case: (pselect (P x)) => [h|h].
- rewrite /inter_right free_map_basis.
  have e : inter_right_fun (exist _ x (conj h hx)) = exist _ x hx by apply: binary_subset_ext.
  by rewrite e subrr.
- rewrite linear0 subr0; congr (free_basis R _); apply: binary_subset_ext; reflexivity.
Qed.

Lemma union_projection_sum (c : free_module R union_set) :
  union_left (project_left c) + union_right (project_right c) = c.
Proof.
apply (free_lift_ext
  (g := (union_reassembly : {linear _ -> _}))
  (h := (idfun : {linear free_module R union_set -> _}))).
move=> [x hx].
change (union_left (project_left (free_basis R (exist (fun x => P x \/ Q x) x hx))) +
  union_right (project_right (free_basis R (exist (fun x => P x \/ Q x) x hx))) =
  free_basis R (exist (fun x => P x \/ Q x) x hx)).
rewrite project_left_basis project_right_basis /left_basis /right_basis /=.
case: (pselect (P x)) => [h|h].
- rewrite linear0 addr0 /union_left free_map_basis.
  congr (free_basis R _); apply: binary_subset_ext; reflexivity.
- rewrite linear0 add0r /union_right free_map_basis.
  congr (free_basis R _); apply: binary_subset_ext; reflexivity.
Qed.

Theorem union_kernel (a : free_module R left_set) (b : free_module R right_set) :
  union_left a + union_right b = 0 ->
    exists c : free_module R inter_set, inter_left c = a /\ - inter_right c = b.
Proof.
move=> h.
have ha := congr1 project_left h.
rewrite linearD project_left_left project_left_right linear0 in ha.
have hb := congr1 project_right h.
rewrite linearD project_right_left project_right_right add0r linear0 in hb.
exists (- project_inter b); split.
- rewrite linearN; apply/eqP; rewrite eq_sym -addr_eq0; apply/eqP; exact ha.
- rewrite linearN opprK; apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP; exact hb.
Qed.

Theorem union_surjective (c : free_module R union_set) :
  exists a b, union_left a + union_right b = c.
Proof. exists (project_left c), (project_right c); exact: union_projection_sum. Qed.

End Binary.
End DPFreeModuleBinaryUnion.
