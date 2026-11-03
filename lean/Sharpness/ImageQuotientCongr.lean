import Sharpness.LinearImageQuotient

/-! Image quotients are preserved by an actual commuting triple of
linear equivalences. The induced map and its formula on representatives
are constructed, for use with the absolute/relative cohomology comparison. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {R A B H A' B' H' : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup H] [Module R H] [AddCommGroup A'] [Module R A']
    [AddCommGroup B'] [Module R B'] [AddCommGroup H'] [Module R H']
    (v : A →ₗ[R] H) (v' : A' →ₗ[R] H')
    (eA : A ≃ₗ[R] A') (eH : H ≃ₗ[R] H')
    (hv : ∀ a, v' (eA a) = eH (v a))

def imageRangeEquiv : v.range ≃ₗ[R] v'.range where
  toFun x := ⟨eH x.val, by
    obtain ⟨a, ha⟩ := x.property
    exact ⟨eA a, (hv a).trans (congrArg eH ha)⟩⟩
  invFun y := ⟨eH.symm y.val, by
    obtain ⟨a, ha⟩ := y.property
    refine ⟨eA.symm a, ?_⟩
    apply eH.injective
    exact (hv (eA.symm a)).symm.trans
      ((congrArg v' (eA.apply_symm_apply a)).trans (ha.trans (eH.apply_symm_apply y.val).symm))⟩
  left_inv x := Subtype.ext (eH.symm_apply_apply x.val)
  right_inv x := Subtype.ext (eH.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (eH.map_add x.val y.val)
  map_smul' r x := Subtype.ext (eH.map_smul r x.val)

variable (u : B →ₗ[R] A) (u' : B' →ₗ[R] A') (eB : B ≃ₗ[R] B')
    (hu : ∀ b, u' (eB b) = eA (u b))

include eB hu in
theorem imageRangeEquiv_map_submodule :
    ((v.comp u).range.comap v.range.subtype).map (imageRangeEquiv v v' eA eH hv).toLinearMap =
      (v'.comp u').range.comap v'.range.subtype := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hx
    refine ⟨eB b, ?_⟩
    exact (congrArg v' (hu b)).trans ((hv (u b)).trans (congrArg eH hb))
  · intro hy
    obtain ⟨b, hb⟩ := hy
    refine ⟨(imageRangeEquiv v v' eA eH hv).symm y, ?_,
      (imageRangeEquiv v v' eA eH hv).apply_symm_apply y⟩
    refine ⟨eB.symm b, ?_⟩
    have he : eH (v (u (eB.symm b))) = y.val :=
      (hv (u (eB.symm b))).symm.trans
        ((congrArg v' (hu (eB.symm b)).symm).trans
          ((congrArg (fun t => v' (u' t)) (eB.apply_symm_apply b)).trans hb))
    change v (u (eB.symm b)) = eH.symm y.val
    simpa only [LinearEquiv.symm_apply_apply] using congrArg eH.symm he

def imageQuotientCongr : ImageQuotient u v ≃ₗ[R] ImageQuotient u' v' :=
  Submodule.Quotient.equiv _ _ (imageRangeEquiv v v' eA eH hv)
    (imageRangeEquiv_map_submodule v v' eA eH hv u u' eB hu)

theorem imageQuotientCongr_projection (a : A) :
    imageQuotientCongr v v' eA eH hv u u' eB hu (imageQuotientProjection u v a) =
      imageQuotientProjection u' v' (eA a) := by
  change Submodule.Quotient.mk ((imageRangeEquiv v v' eA eH hv) ⟨v a, ⟨a, rfl⟩⟩) =
    Submodule.Quotient.mk (⟨v' (eA a), ⟨eA a, rfl⟩⟩ : v'.range)
  exact congrArg (fun x : v'.range => Submodule.Quotient.mk x) (Subtype.ext (hv a).symm)

end Sharpness
