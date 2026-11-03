(** Divisibility implies the genuine extension property for integer modules.
    This uses the proved integer-ideal theorem and Baer's proved criterion. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules ModuleInfrastructure
  MackeyModuleCarriers ModuleInjectives ModuleBaer ModuleIntegerIdeals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition integer_module_divisible (J : lmodType int) :=
  forall (n : nat) (x : J), (0 < n)%N -> exists y : J, y *+ n = x.

Theorem divisible_integer_module_injective (J : lmodType int) :
    integer_module_divisible J -> module_injective J.
Proof.
  intro divJ. apply baer_implies_injective. intros N f.
  destruct (integer_ideal_principal N) as [d [hd he]].
  destruct d as [|d].
  - exists (module_element_hom (0 : J)). intro z.
    destruct ((proj1 (he (submodule_val z))) (submodule_val_mem z)) as [q hq].
    have hz : z = 0.
    { apply submodule_val_injective. change (submodule_val z = 0).
      by rewrite hq mulr0. }
    rewrite hz. change (module_element_hom (0 : J) 0 = f 0).
    by rewrite !module_hom_zero.
  - pose (zd := @submodule_in int [the lmodType int of int^o] N (d.+1 : int) hd).
    destruct (divJ d.+1 (f zd) (ltn0Sn d)) as [y hy].
    have hdy : (d.+1 : int) *: y = f zd.
    { have hs := @scaler_int int J (d.+1 : int) y.
      rewrite intz in hs. rewrite hs. exact hy. }
    exists (module_element_hom y). intro z.
    destruct ((proj1 (he (submodule_val z))) (submodule_val_mem z)) as [q hq].
    have hz : z = q *: zd.
    { apply submodule_val_injective.
      change ((submodule_val z : int) = q * (d.+1 : int)). exact hq. }
    change ((submodule_val z : int) *: y = f z).
    rewrite hq -scalerA hdy hz module_hom_scale.
    reflexivity.
Qed.
