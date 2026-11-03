(** Genuine finite-diagonal model presentation of the actual total complex. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear BarFreeModule.
From DiazParkV16b Require Import ChainComplex ModelwisePresentation BisimplicialSet BisimplicialChains
  BisimplicialRepresentable BisimplicialChainDiagrams BisimplicialDegreePresentation
  FirstQuadrantChainTotal FirstQuadrantChainTotalMaps FirstQuadrantChainTotalSupport
  FirstQuadrantChainTotalProjective.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPModelwisePresentation DPBisimplicialSet
  DPBisimplicialChains DPBisimplicialRepresentable DPBisimplicialChainDiagrams DPBisimplicialDegreePresentation
  DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainSupport DPFirstQuadrantChainTotalProjective.
Local Open Scope ring_scope.

Module DPBisimplicialTotalPresentation.
Section Presentation.
Variable R : pzRingType.

Definition total_inclusion p q n (h : (p+q)%coq_nat=n) :
  nat_trans (bisimplex_degree R p q) (total_degree R n).
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (bisimplex_degree R p q) (total_degree R n)
  (fun X => module_hom_of_linear (@total_include R (bisimplicial_bicomplex R X) p q n h)) _).
move=> X Y a; apply module_hom_ext => x.
apply functional_extensionality_dep => r; apply functional_extensionality_dep => s;
  apply functional_extensionality_dep => e.
change (@total_include R (bisimplicial_bicomplex R Y) p q n h
  (free_map R (bisimplex_component a p q) x) r s e =
  free_map R (bisimplex_component a r s) (@total_include R (bisimplicial_bicomplex R X) p q n h x r s e)).
case (Nat.eq_dec p r) => [hp|hp].
- subst r.
  have hs : q=s by lia.
  subst s.
  by rewrite !total_include_same.
- by rewrite !total_include_other // linear0.
Defined.

Definition total_model n (i : 'I_n.+1) : bisimplicial_category :=
  representable (val i) (diagonal_second i).
Definition total_generator n (i : 'I_n.+1) : fobj (total_degree R n) (total_model i) :=
  @total_include R (bisimplicial_bicomplex R (total_model i)) (val i) (diagonal_second i) n
    (diagonal_equation i) (degree_generator R (val i) (diagonal_second i)).

Variable n : nat.
Variable F : module_diagram R bisimplicial_category.
Variable v : forall i : 'I_n.+1, fobj F (total_model i).

Definition total_lift_component (X : bisimplicial_category) : module_hom (fobj (total_degree R n) X) (fobj F X).
Proof.
exists (fun x => \sum_(i : 'I_n.+1) module_hom_fun (component (degree_lift (v i)) X)
  (x (val i) (diagonal_second i) (diagonal_equation i))).
move=> r x y; rewrite scaler_sumr -big_split.
apply eq_bigr => i _; exact: module_hom_linear.
Defined.

Definition total_lift : nat_trans (total_degree R n) F.
Proof.
refine (@Build_nat_trans bisimplicial_category (module_category R) (total_degree R n) F total_lift_component _).
move=> X Y a; apply module_hom_ext => x.
change ((\sum_(i : 'I_n.+1) module_hom_fun (component (degree_lift (v i)) Y)
  (free_map R (bisimplex_component a (val i) (diagonal_second i))
    (x (val i) (diagonal_second i) (diagonal_equation i)))) =
  module_hom_fun (fmap F a) (\sum_(i : 'I_n.+1) module_hom_fun (component (degree_lift (v i)) X)
    (x (val i) (diagonal_second i) (diagonal_equation i)))).
rewrite linear_sum; apply eq_bigr => i _.
exact (f_equal (fun t : module_hom (fobj (bisimplex_degree R (val i) (diagonal_second i)) X) (fobj F Y) =>
  t (x (val i) (diagonal_second i) (diagonal_equation i))) (naturality (degree_lift (v i)) a)).
Defined.

Lemma total_lift_generator (j : 'I_n.+1) :
  module_hom_fun (component total_lift (total_model j)) (total_generator j) = v j.
Proof.
change ((\sum_(i : 'I_n.+1) module_hom_fun (component (degree_lift (v i)) (total_model j))
  ((total_generator j) (val i) (diagonal_second i) (diagonal_equation i))) = v j).
rewrite (bigD1 j) //= /total_generator total_include_same.
rewrite /degree_generator free_lift_basis characteristic_generator fmap_id.
have hz : \sum_(i : 'I_n.+1 | i != j) module_hom_fun (component (degree_lift (v i)) (total_model j))
  (@total_include R (bisimplicial_bicomplex R (total_model j)) (val j) (diagonal_second j) n
    (diagonal_equation j) (degree_generator R (val j) (diagonal_second j))
    (val i) (diagonal_second i) (diagonal_equation i)) = 0.
  apply big1 => i hij.
  have hne : val j <> val i.
    move=> he; have e : i=j by apply val_inj; symmetry; exact he.
    by rewrite e eqxx in hij.
  by rewrite total_include_other // module_hom_zero.
by rewrite hz addr0.
Qed.

Lemma total_hom_ext (a b : nat_trans (total_degree R n) F) :
  (forall i, module_hom_fun (component a (total_model i)) (total_generator i) =
    module_hom_fun (component b (total_model i)) (total_generator i)) -> a=b.
Proof.
move=> hg.
have hi (i : 'I_n.+1) : nat_comp (total_inclusion (diagonal_equation i)) a =
  nat_comp (total_inclusion (diagonal_equation i)) b.
  apply (@model_hom_ext R bisimplicial_category unit (degree_model (val i) (diagonal_second i))
    (bisimplex_degree R (val i) (diagonal_second i)) (degree_presentation R (val i) (diagonal_second i)) F _ _) => u.
  case: u; exact (hg i).
apply nat_trans_ext => X; apply module_hom_ext => x.
rewrite -[x](total_diagonal_decomposition x) !linear_sum.
apply eq_bigr => i _.
exact (f_equal (fun t : nat_trans (bisimplex_degree R (val i) (diagonal_second i)) F =>
  module_hom_fun (component t X) (x (val i) (diagonal_second i) (diagonal_equation i))) (hi i)).
Qed.
End Presentation.

Definition total_presentation (R : pzRingType) n :
  model_presentation (@total_model n) (total_degree R n).
Proof.
refine (@ModelPresentation R bisimplicial_category 'I_n.+1 (@total_model n) (total_degree R n)
  (@total_generator R n) (fun F v => total_lift v) _ _).
- move=> F v i; exact: total_lift_generator.
- move=> F a b h; exact: total_hom_ext h.
Defined.
End DPBisimplicialTotalPresentation.
