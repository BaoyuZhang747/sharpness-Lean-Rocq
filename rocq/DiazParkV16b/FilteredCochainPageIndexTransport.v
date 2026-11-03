(** Actual integer-index transport, including the incoming differential. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles DPFilteredPages DPFilteredPageHomology.
Local Open Scope ring_scope.

Module DPFilteredPageIndexTransport.
Section Transport.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Definition page_index_iso r p q n (h : p=q) : @isomorphism (module_category R) (page F r p n) (page F r q n).
Proof. destruct h; exact (@iso_refl (module_category R) (page F r p n)). Defined.

Lemma page_index_iso_hom r p q n (h : p=q) x :
    module_hom_fun (iso_hom (page_index_iso r n h)) x=page_index_cast F r n h x.
Proof. destruct h; reflexivity. Qed.

Lemma page_index_cast_injective r p q n (h : p=q) : injective (page_index_cast F r n h).
Proof. destruct h; exact (fun x y hxy => hxy). Qed.

Lemma page_incoming_after_cast r p q n (h : Z.sub p (Z.of_nat r.+1)=q)
    (h' : Z.add q (Z.of_nat r.+1)=p) (x : page F r (Z.sub p (Z.of_nat r.+1)) n) :
    page_incoming x=page_index_cast F r n.+1 h' (page_d F r q n (page_index_cast F r n h x)).
Proof.
destruct h.
have he : h'=incoming_index r p by apply Prop_irrelevance.
rewrite he; reflexivity.
Qed.

End Transport.
End DPFilteredPageIndexTransport.
