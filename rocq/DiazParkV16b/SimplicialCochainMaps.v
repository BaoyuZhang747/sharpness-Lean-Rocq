(** Literal pullbacks and coefficient maps on function cochains. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category HomologicalComplex HomologicalCohomologyMaps.
From DiazParkV16b Require Import SimplicialSet SimplicialSetOperators
  SimplicialChains SimplicialCochains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPSimplicialSet DPSimplicialOperators
  DPSimplicialChains DPSimplicialCochains.
Local Open Scope ring_scope.

Module DPSimplicialCochainMaps.
Section Pullback.
Variable R : pzRingType.
Variables X Y : simplicial_set.
Variable f : simplicial_map X Y.
Variable A : lmodType R.

Definition pull_at n (a : cochain_functions Y A n) : cochain_functions X A n :=
  fun x => a (component f n x).
Lemma pull_linear n : linear (@pull_at n).
Proof. move=> r a b; apply functional_extensionality_dep => x; reflexivity. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (cochain_functions Y A n)
  (cochain_functions X A n) _ (@pull_at n) (@pull_linear n).

Definition pull : cochain_map (complex Y A) (complex X A).
Proof.
refine (@CochainMap R (complex Y A) (complex X A) (fun n => @pull_at n) _).
move=> n a; apply functional_extensionality_dep => x.
change (cochain_d (complex X A) n (@pull_at n a) x =
  cochain_d (complex Y A) n a (component f n.+1 x)).
rewrite !differential_at /pull_at.
apply eq_bigr => i _; congr (_ *: _); congr (a _).
exact: simplicial_map_face.
Defined.

Lemma pull_at_formula n (a : cochain_functions Y A n) x :
  cochain_map_at pull n a x = a (component f n x).
Proof. reflexivity. Qed.
End Pullback.

Section Coefficients.
Variable R : pzRingType.
Variable X : simplicial_set.
Variables A B : lmodType R.
Variable f : {linear A -> B}.

Definition coefficient_at n (a : cochain_functions X A n) : cochain_functions X B n :=
  fun x => f (a x).
Lemma coefficient_linear n : linear (@coefficient_at n).
Proof.
move=> r a b; apply functional_extensionality_dep => x.
change (f (r *: a x + b x) = r *: f (a x) + f (b x)); exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (cochain_functions X A n)
  (cochain_functions X B n) _ (@coefficient_at n) (@coefficient_linear n).

Definition coefficient : cochain_map (complex X A) (complex X B).
Proof.
refine (@CochainMap R (complex X A) (complex X B) (fun n => @coefficient_at n) _).
move=> n a; apply functional_extensionality_dep => x.
change (cochain_d (complex X B) n (@coefficient_at n a) x =
  f (cochain_d (complex X A) n a x)).
rewrite !differential_at /coefficient_at linear_sum.
apply eq_bigr => i _; by rewrite linearZ.
Defined.
End Coefficients.

Section Laws.
Variable R : pzRingType.
Variable A : lmodType R.
Lemma pull_identity (X : simplicial_set) n (a : cochain_functions X A n) :
  cochain_map_at (pull (nat_id X) A) n a = a.
Proof. by apply functional_extensionality_dep => x. Qed.

Lemma pull_composition (X Y Z : simplicial_set)
    (f : simplicial_map X Y) (g : simplicial_map Y Z) n (a : cochain_functions Z A n) :
  cochain_map_at (pull (nat_comp f g) A) n a =
    cochain_map_at (pull f A) n (cochain_map_at (pull g A) n a).
Proof. by apply functional_extensionality_dep => x. Qed.

Lemma pull_coefficient (X Y : simplicial_set) (f : simplicial_map X Y)
    (B : lmodType R) (u : {linear A -> B}) n (a : cochain_functions Y A n) :
  cochain_map_at (coefficient X u) n (cochain_map_at (pull f A) n a) =
    cochain_map_at (pull f B) n (cochain_map_at (coefficient Y u) n a).
Proof. by apply functional_extensionality_dep => x. Qed.
End Laws.
End DPSimplicialCochainMaps.
