(** Actual total maps, row/column complexes and literal component formulas. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazParkV16b Require Import ChainComplex FirstQuadrantChainBicomplex FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPFirstQuadrantChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.
Module DPFirstQuadrantChainTotalMaps.
Section Maps.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.
Definition total_map_at n (a : total_term K n) : total_term L n :=
  fun p q h => bicomplex_map_at f p q (a p q h).
Lemma total_map_at_linear n : linear (@total_map_at n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change (bicomplex_map_at f p q (r *: a p q h+b p q h) =
 r *: bicomplex_map_at f p q (a p q h)+bicomplex_map_at f p q (b p q h)).
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@total_map_at n) (@total_map_at_linear n).
Definition total_map : chain_map (total_complex K) (total_complex L).
Proof.
refine (@ChainMap R (total_complex K) (total_complex L) (fun n => (@total_map_at n : {linear _ -> _})) _).
move=> n a; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change (horizontal L p q (bicomplex_map_at f p.+1 q (a p.+1 q (horizontal_input h))) +
 (-1:R)^+p *: vertical L p q (bicomplex_map_at f p q.+1 (a p q.+1 (vertical_input h))) =
 bicomplex_map_at f p q (horizontal K p q (a p.+1 q (horizontal_input h)) +
 (-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h)))).
by rewrite linearD linearZ bicomplex_map_horizontal bicomplex_map_vertical.
Defined.
End Maps.
Section Columns.
Variable R : pzRingType.
Variable K : bicomplex R.
Definition vertical_complex p : chain_complex R :=
 @ChainComplex R (bicomplex_term K p) (vertical K p) (@vertical_squared R K p).
Definition horizontal_complex q : chain_complex R :=
 @ChainComplex R (fun p => bicomplex_term K p q) (fun p => horizontal K p q)
 (fun p => @horizontal_squared R K p q).
End Columns.
Section ColumnMaps.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.
Definition vertical_map p : chain_map (vertical_complex K p) (vertical_complex L p) :=
 @ChainMap R (vertical_complex K p) (vertical_complex L p) (fun q => bicomplex_map_at f p q) (@bicomplex_map_vertical R K L f p).
Definition horizontal_map q : chain_map (horizontal_complex K q) (horizontal_complex L q) :=
 @ChainMap R (horizontal_complex K q) (horizontal_complex L q) (fun p => bicomplex_map_at f p q) (fun p => @bicomplex_map_horizontal R K L f p q).
End ColumnMaps.
End DPFirstQuadrantChainTotalMaps.
