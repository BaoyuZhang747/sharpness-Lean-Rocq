From mathcomp Require Import all_boot all_algebra all_fingroup boolp pgroup.
From DiazPark Require Import ModuleInfrastructure MackeyGroupAction MackeyGroupActionFixed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Section FixedSubmodule.
Variable R : pzRingType.
Variable G : finGroupType.
Variable V : lmodType R.
Variable rho : right_linear_action G V.
Variable H : {group G}.

Definition fixed_submodule : module_subspace V.
Proof.
refine (@ModuleSubspace R V
  (fun x => forall g, g \in H -> right_action rho g x = x) _ _ _).
- by move=> g hg; rewrite linear0.
- by move=> x y hx hy g hg; rewrite linearD hx // hy.
- by move=> a x hx g hg; rewrite linearZ hx.
Defined.

Lemma normal_fixed_submodule_invariant :
    H <| [set: G] -> action_invariant rho fixed_submodule.
Proof.
move=> /andP[_ hn] g x hx h hh.
have hng : (g^-1)%g \in 'N(H) := subsetP hn (g^-1)%g (in_setT _).
have hconj : (h ^ g^-1)%g \in H by rewrite memJ_norm.
have he : ((h ^ g^-1) * g = g*h)%g.
  by rewrite conjgE invgK -mulgA mulgKV.
change (right_action rho h (right_action rho g x) = right_action rho g x).
by rewrite -right_action_mul -he right_action_mul (hx _ hconj).
Qed.

End FixedSubmodule.

Section NormalPTrivial.
Variable K : fieldType.
Variable G : finGroupType.
Variable V : lmodType K.
Variable rho : right_linear_action G V.

Theorem simple_action_normal_p_trivial p (hp : p \in [pchar K])
    (H : {group G}) : H <| [set: G] -> p.-group H -> action_simple rho ->
    forall g, g \in H -> forall x, right_action rho g x = x.
Proof.
move=> hn hH [hnz hs].
have [v [hv hfix]] := @arbitrary_action_pgroup_fixed K G V rho p hp H hH hnz.
case: (hs (fixed_submodule rho H) (@normal_fixed_submodule_invariant K G V rho H hn)) => h.
- exfalso; exact: hv (h v hfix).
- by move=> g hg x; exact: h x g hg.
Qed.

End NormalPTrivial.
