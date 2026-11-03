(** The actual cochain replacement of a diagram of cochain complexes.
    Horizontal degree is category-bar degree; vertical degree is the original
    cochain degree. Products range over all actual category strings. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarComplex BarNaturality
  HomologicalDiagramInjectives CategoryInjectiveResolutionComparison.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarComplex DiazParkBarNaturality DPFirstQuadrantCochain.
Local Open Scope ring_scope.

Section Replacement.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).

Definition cochain_replacement_term p q : lmodType R := bar_term (diagram_term K q) p.

Lemma cochain_replacement_vertical_squared p q (v : cochain_replacement_term p q) :
    bar_map_at (diagram_d K q.+1) (bar_map_at (diagram_d K q) v) = 0.
Proof.
apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s.
exact (@diagram_d2 R (opposite C) K q c (v c s)).
Qed.

Definition cochain_replacement_bicomplex : bicomplex R :=
  @Bicomplex R cochain_replacement_term
    (fun p q => bar_d (diagram_term K q) p)
    (fun p q => (@bar_map_at R C _ _ (diagram_d K q) p : {linear _ -> _}))
    (fun p q v => @bar_d_squared R C (diagram_term K q) p v)
    cochain_replacement_vertical_squared
    (fun p q v => @bar_map_d R C _ _ (diagram_d K q) p v).
End Replacement.

Section Maps.
Variable R : pzRingType.
Variable C : category.
Variables K L : @diagram_complex R (opposite C).
Variable f : diagram_cochain_map K L.

Definition cochain_replacement_map : bicomplex_map
    (cochain_replacement_bicomplex K) (cochain_replacement_bicomplex L).
Proof.
refine (@BicomplexMap R (cochain_replacement_bicomplex K)
  (cochain_replacement_bicomplex L)
  (fun p q => (@bar_map_at R C _ _ (diagram_cochain_map_at f q) p : {linear _ -> _})) _ _).
- intros p q v; exact: bar_map_d.
- intros p q v; apply functional_extensionality_dep; intro c.
  apply functional_extensionality_dep; intro s.
  exact (diagram_cochain_map_commutes f q c (v c s)).
Defined.
End Maps.
