(** Literal coordinate isomorphism from F^p/F^{p+1} in total degree q+p
    to the (p,q) entry of the original bicomplex. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainSpectralRelative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFirstQuadrantCochain
  DPFirstQuadrantTotal DPFirstQuadrantSupport DPColumnFiltration DPColumnRelative.
Local Open Scope ring_scope.

Module DPColumnCoordinate.
Section Coordinate.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition column_coordinate p q (x : column_term K p (q+p)%coq_nat) : bicomplex_term K p q :=
  submodule_val x p q (Nat.add_comm p q).

Lemma column_coordinate_linear p q : linear (@column_coordinate p q).
Proof. intros a x y; reflexivity. Qed.
HB.instance Definition _ p q := GRing.isLinear.Build R (column_term K p (q+p)%coq_nat)
  (bicomplex_term K p q) _ (@column_coordinate p q) (@column_coordinate_linear p q).

Lemma column_coordinate_kernel p q (x : column_term K p (q+p)%coq_nat) :
    relative_subspace K p p.+1 (q+p)%coq_nat x <-> column_coordinate x = 0.
Proof.
split.
- intro hx; apply hx; lia.
- intros hx r s h hrs.
  destruct (Nat.eq_dec r p) as [hr|hr].
  + subst r.
    have hs : s = q by lia. subst s.
    have he : h = Nat.add_comm p q by apply Prop_irrelevance.
    rewrite he; exact hx.
  + apply (submodule_val_mem x); lia.
Qed.

Definition column_coordinate_section p q (x : bicomplex_term K p q) : column_term K p (q+p)%coq_nat :=
  @submodule_in R (total_term K (q+p)%coq_nat) (column_subspace K p (q+p)%coq_nat)
    (total_include (Nat.add_comm p q) x) (total_include_supported (Nat.add_comm p q) x).

Lemma column_coordinate_section_spec p q (x : bicomplex_term K p q) :
    column_coordinate (column_coordinate_section x) = x.
Proof. exact: total_include_same. Qed.

Definition column_coordinate_iso p q : @isomorphism (module_category R)
    (relative_term K p p.+1 (q+p)%coq_nat) (bicomplex_term K p q) :=
  @quotient_linear_iso R (column_term K p (q+p)%coq_nat) (bicomplex_term K p q)
    (relative_subspace K p p.+1 (q+p)%coq_nat) (@column_coordinate p q)
    (@column_coordinate_kernel p q)
    (fun x => ex_intro _ (column_coordinate_section x) (column_coordinate_section_spec x)).

Lemma column_coordinate_iso_pi p q (x : column_term K p (q+p)%coq_nat) :
    module_hom_fun (iso_hom (column_coordinate_iso p q))
      (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat) x) = column_coordinate x.
Proof. exact: quotient_iso_map_pi. Qed.

Lemma column_coordinate_d p q (x : column_term K p (q+p)%coq_nat) :
    @column_coordinate p q.+1 (@column_d R K p (q+p)%coq_nat x) =
      (-1 : R)^+p *: vertical K p q (column_coordinate x).
Proof.
unfold column_coordinate.
destruct p as [|p].
- change (0 + (-1 : R)^+0 *: vertical K 0%N q
    (submodule_val x 0%N q (vertical_index (Nat.add_comm 0%N q.+1))) =
    (-1 : R)^+0 *: vertical K 0%N q (submodule_val x 0%N q (Nat.add_comm 0%N q))).
  have he : vertical_index (Nat.add_comm 0%N q.+1) = Nat.add_comm 0%N q
    by apply Prop_irrelevance.
  by rewrite he add0r.
- change (horizontal K p q.+1 (submodule_val x p q.+1 (horizontal_index (Nat.add_comm p.+1 q.+1))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (submodule_val x p.+1 q (vertical_index (Nat.add_comm p.+1 q.+1))) =
    (-1 : R)^+p.+1 *: vertical K p.+1 q (submodule_val x p.+1 q (Nat.add_comm p.+1 q))).
  have hx : submodule_val x p q.+1 (horizontal_index (Nat.add_comm p.+1 q.+1)) = 0.
    apply (submodule_val_mem x); lia.
  have he : vertical_index (Nat.add_comm p.+1 q.+1) = Nat.add_comm p.+1 q
    by apply Prop_irrelevance.
  by rewrite hx he linear0 add0r.
Qed.

End Coordinate.
End DPColumnCoordinate.
