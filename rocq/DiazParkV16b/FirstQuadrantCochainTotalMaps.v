(** Actual maps and the zero-column cochain projection of the finite total. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal.
Local Open Scope ring_scope.

Module DPFirstQuadrantTotalMaps.
Section Maps.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.

Definition total_map_at n (a : total_term K n) : total_term L n :=
  fun p q h => bicomplex_map_at f p q (a p q h).

Lemma total_map_linear n : linear (@total_map_at n).
Proof.
intros r a b; apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (total_term K n) (total_term L n)
  _ (@total_map_at n) (@total_map_linear n).

Lemma total_map_horizontal n (a : total_term K n) :
    total_horizontal (K := L) (total_map_at a) = total_map_at (total_horizontal (K := K) a).
Proof.
apply functional_extensionality_dep; intros [|p].
all: apply functional_extensionality_dep; intro q.
all: apply functional_extensionality_dep; intro h.
- symmetry; exact: linear0.
- exact: bicomplex_map_horizontal.
Qed.

Lemma total_map_vertical n (a : total_term K n) :
    total_vertical (K := L) (total_map_at a) = total_map_at (total_vertical (K := K) a).
Proof.
apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intros [|q].
all: apply functional_extensionality_dep; intro h.
- symmetry; exact: linear0.
- change ((-1 : R)^+p *: vertical L p q (bicomplex_map_at f p q (a p q (vertical_index h))) =
    bicomplex_map_at f p q.+1 ((-1 : R)^+p *: vertical K p q (a p q (vertical_index h)))).
  by rewrite linearZ bicomplex_map_vertical.
Qed.

Lemma total_map_d n (a : total_term K n) :
    total_d (K := L) (total_map_at a) = total_map_at (total_d (K := K) a).
Proof. by rewrite /total_d linearD total_map_horizontal total_map_vertical. Qed.

Definition total_cochain_map : cochain_map (total_complex K) (total_complex L) :=
  @CochainMap R (total_complex K) (total_complex L)
    (fun n => (@total_map_at n : {linear _ -> _})) total_map_d.
End Maps.

Section Projection.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition vertical_complex p : cochain_complex R :=
  @CochainComplex R (bicomplex_term K p) (vertical K p) (@vertical_squared R K p).

Definition zero_column_at n (a : total_term K n) : bicomplex_term K 0%N n :=
  a 0%N n Logic.eq_refl.

Lemma zero_column_linear n : linear (@zero_column_at n).
Proof. by intros r a b. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (total_term K n) (bicomplex_term K 0%N n)
  _ (@zero_column_at n) (@zero_column_linear n).

Lemma zero_column_d n (a : total_term K n) :
    vertical K 0%N n (zero_column_at a) = zero_column_at (total_d (K := K) a).
Proof.
change (vertical K 0%N n (a 0%N n Logic.eq_refl) =
  0 + (-1 : R)^+0 *: vertical K 0%N n
    (a 0%N n (vertical_index (Logic.eq_refl : (0 + n.+1)%coq_nat = n.+1)))).
have h : vertical_index (Logic.eq_refl : (0 + n.+1)%coq_nat = n.+1) = Logic.eq_refl
  by apply Prop_irrelevance.
by rewrite h expr0 scale1r add0r.
Qed.

Definition zero_column_projection : cochain_map (total_complex K) (vertical_complex 0%N) :=
  @CochainMap R (total_complex K) (vertical_complex 0%N)
    (fun n => (@zero_column_at n : {linear _ -> _})) zero_column_d.
End Projection.
End DPFirstQuadrantTotalMaps.
