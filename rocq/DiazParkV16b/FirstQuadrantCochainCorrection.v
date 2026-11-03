(** One genuine finite-diagonal correction removes the leading column of
    a total cocycle, using exactness only on vertical cohomology. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex HomologicalCohomology.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainEdge
  FirstQuadrantCochainLeading FirstQuadrantCochainInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DPFirstQuadrantCochain
  DPFirstQuadrantTotal DPFirstQuadrantTotalMaps DPFirstQuadrantSupport DPFirstQuadrantEdge
  DPFirstQuadrantLeading DPFirstQuadrantInclusion.
Local Open Scope ring_scope.

Module DPFirstQuadrantCorrection.
Section Correction.
Variable R : pzRingType.
Variable K : bicomplex R.
Variable hK : positive_horizontal_exact K.

Theorem leading_correction n p q (hpq : (p + q)%coq_nat = n)
    (x : total_term K n.+1) (hx : cocycle (total_complex K) n.+1 x)
    (hs : supported_from x p.+1) :
    exists y : total_term K n,
      supported_from y p /\ supported_from (total_d y) p.+1 /\
      @total_d R K n y p.+1 q (horizontal_output_index hpq) =
        x p.+1 q (horizontal_output_index hpq).
Proof.
have hv := @leading_vertical_cycle R K n.+1 p.+1 q (horizontal_output_index hpq) x hx hs.
have hh := @leading_horizontal_cycle R K n.+1 p.+1 q (horizontal_output_index hpq) x hx hs.
have hev : hv = @leading_vertical_cycle R K n.+1 p.+1 q (horizontal_output_index hpq) x hx hs
  by apply Prop_irrelevance.
rewrite <- hev in hh.
have [a [ha hb]] := @horizontal_cycle_lift R K hK p q
  (x p.+1 q (horizontal_output_index hpq)) hv hh.
destruct q as [|q].
- exists (total_include hpq a).
  split; [exact: total_include_supported|].
  split; [exact: include_cycle_d_supported|].
  rewrite include_d_horizontal.
  change (x p.+1 0%N (horizontal_output_index hpq) - horizontal K p 0%N a = 0) in hb.
  symmetry; exact (subr0_eq hb).
- destruct hb as [b hb].
  have hsecond : (p.+1 + q)%coq_nat = n by lia.
  pose y1 : total_term K n := total_include hpq a.
  pose y2 : total_term K n := (-1 : R)^+p.+1 *: total_include hsecond b.
  have hy1 : supported_from y1 p := total_include_supported hpq a.
  have hy2 : supported_from y2 p.+1.
    apply supported_from_scale; exact: total_include_supported.
  have hd1 : supported_from (total_d y1) p.+1 := include_cycle_d_supported hpq ha.
  have hd2 : supported_from (total_d y2) p.+1 := total_d_supported hy2.
  exists (y1 + y2).
  split.
  + apply supported_from_add; [exact hy1|].
    apply (supported_from_mono hy2); lia.
  + split.
    * rewrite linearD; exact: supported_from_add hd1 hd2.
    * rewrite /y1 /y2 linearD linearZ.
      change (@total_d R K n (total_include hpq a) p.+1 q.+1 (horizontal_output_index hpq) +
        (-1 : R)^+p.+1 *: @total_d R K n (total_include hsecond b)
          p.+1 q.+1 (horizontal_output_index hpq) = x p.+1 q.+1 (horizontal_output_index hpq)).
      rewrite include_d_horizontal.
      have he : horizontal_output_index hpq = vertical_output_index hsecond by apply Prop_irrelevance.
      rewrite he include_d_vertical sign_scale_cancel.
      change (vertical K p.+1 q b = x p.+1 q.+1 (horizontal_output_index hpq) - horizontal K p q.+1 a) in hb.
      rewrite hb -he.
      by rewrite addrC subrK.
Qed.
End Correction.
End DPFirstQuadrantCorrection.
