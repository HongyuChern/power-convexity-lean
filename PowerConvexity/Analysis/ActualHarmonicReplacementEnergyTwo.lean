import PowerConvexity.Analysis.ActualWeakDomainRepresentativeTwo

/-! # Actual energy error of harmonic replacement.
The weak variable-coefficient solution and the actual smooth Laplacian
replacement have the same Sobolev boundary datum. Their gradient error is
bounded by the actual coefficient oscillation times the original energy.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_coeffAction_memLp_two {U : Set F} (A : EllipticCoeff (2+2) U)
    {g : F → F} (hg : MemLp g 2 (volume.restrict U)) :
    MemLp (fun x => matMulE (A.a x) (g x)) 2 (volume.restrict U) := by
  have hbound : ∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖matMulE (A.a x) z‖ ≤ A.Λ*‖z‖ := by
    filter_upwards [A.mixed_bound] with x hx
    intro z
    let y := matMulE (A.a x) z
    have hh := hx z y
    have he : |⟪y,y⟫_ℝ| = ‖y‖^2 := by rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)]
    change |⟪y,y⟫_ℝ| ≤ A.Λ*‖y‖*‖z‖ at hh
    rw [he] at hh
    change ‖y‖ ≤ A.Λ*‖z‖
    nlinarith [norm_nonneg y,mul_nonneg A.Λ_nonneg (norm_nonneg z)]
  apply MemLp.of_eval_piLp
  intro i
  apply MemLp.of_le_mul (g := fun x => ‖g x‖) (c := A.Λ) hg.norm
  · have hgc : Continuous (fun y : F => (WithLp.ofLp y : Fin (2+2) → ℝ)) :=
      PiLp.continuous_ofLp 2 (fun _ : Fin (2+2) => ℝ)
    have hgpi := hgc.comp_aestronglyMeasurable hg.aestronglyMeasurable
    have hm : AEMeasurable (fun x => ∑ j : Fin (2+2), A.a x i j*(g x).ofLp j)
        (volume.restrict U) := by
      have hh : AEMeasurable (∑ j : Fin (2+2), fun x => A.a x i j*(g x).ofLp j)
          (volume.restrict U) := by
        apply Finset.aemeasurable_sum
        intro j _
        exact (A.measurable_apply i j).aemeasurable.mul
          ((continuous_apply j).comp_aestronglyMeasurable hgpi).aemeasurable
      convert hh using 1
      ext x
      simp
    exact hm.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun x => by
      simp only [matMulE_apply,Matrix.mulVec]
      rfl))
  · filter_upwards [hbound] with x hx
    exact (PiLp.norm_apply_le (matMulE (A.a x) (g x)) i).trans (by simpa using hx (g x))

theorem actual_coeffMulLpL_ae_two {U : Set F} (A : EllipticCoeff (2+2) U)
    (G : Lp F 2 (volume.restrict U)) :
    coeffMulLpL A G =ᵐ[volume.restrict U] (fun x => matMulE (A.a x) (G x)) := by
  exact MemLp.coeFn_toLp (actual_coeffAction_memLp_two A (Lp.memLp G))

theorem actual_coeffMulLpL_identity_two {U : Set F}
    (G : Lp F 2 (volume.restrict U)) :
    coeffMulLpL (identityNormalizedEllipticCoeffTwo U).1 G = G := by
  apply Lp.ext
  filter_upwards [actual_coeffMulLpL_ae_two (identityNormalizedEllipticCoeffTwo U).1 G] with x hx
  simpa [identityNormalizedEllipticCoeffTwo,matMulE,Matrix.one_mulVec] using hx

theorem actual_coefficient_energy_difference_two {U : Set F} (A : EllipticCoeff (2+2) U)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖)
    (G : Lp F 2 (volume.restrict U)) :
    ‖G-coeffMulLpL A G‖ ≤ delta*‖G‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub G (coeffMulLpL A G),actual_coeffMulLpL_ae_two A G,hA] with x hx hax hb
  rw [hx,Pi.sub_apply,hax]
  exact hb (G x)

theorem actual_harmonic_replacement_energy_bound_two
    {U : Set F} (A : EllipticCoeff (2+2) U) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖)
    {u v : F → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (hv : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v)
    (hzero : MemH01 (fun x => u x-v x) U)
    (uw : MemW1pWitness 2 u U) (vw : MemW1pWitness 2 v U) :
    ‖gradLpOfWitness uw-gradLpOfWitness vw‖ ≤ delta*‖gradLpOfWitness uw‖ := by
  let G := gradLpOfWitness uw
  let H := gradLpOfWitness vw
  let D := G-H
  have hae : (fun x => u x+(-1)*v x) =ᵐ[volume.restrict U] (fun x => u x-v x) :=
    Filter.Eventually.of_forall (fun x => by ring)
  let dw := MemW1pWitness.ofAeEq hae (uw.add (vw.smul (-1)))
  have hD : gradLpOfWitness dw = D := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp dw.weakGrad_memLp,MemLp.coeFn_toLp uw.weakGrad_memLp,
      MemLp.coeFn_toLp vw.weakGrad_memLp,Lp.coeFn_sub G H] with x hd hu' hv' hs
    change (gradLpOfWitness dw) x = (G-H) x
    rw [hs]
    change dw.weakGrad_memLp.toLp dw.weakGrad x =
      uw.weakGrad_memLp.toLp uw.weakGrad x-vw.weakGrad_memLp.toLp vw.weakGrad x
    rw [hd,hu',hv']
    change uw.weakGrad x+(-1 : ℝ) • vw.weakGrad x = uw.weakGrad x-vw.weakGrad x
    simp [sub_eq_add_neg]
  have htestA : ⟪coeffMulLpL A G,D⟫_ℝ = 0 := by
    rw [← hD]
    exact (coeffMulLpL_inner_gradLpOfWitness_eq_bilinFormOfCoeff A uw dw).trans
      (hu.2 uw _ hzero dw)
  have htestH : ⟪H,D⟫_ℝ = 0 := by
    rw [← hD,← actual_coeffMulLpL_identity_two H]
    exact (coeffMulLpL_inner_gradLpOfWitness_eq_bilinFormOfCoeff
      (identityNormalizedEllipticCoeffTwo U).1 vw dw).trans (hv.2 vw _ hzero dw)
  have he : ⟪D,D⟫_ℝ = ⟪G-coeffMulLpL A G,D⟫_ℝ := by
    calc
      ⟪D,D⟫_ℝ = ⟪G,D⟫_ℝ-⟪H,D⟫_ℝ := inner_sub_left _ _ _
      _ = ⟪G,D⟫_ℝ := by rw [htestH,sub_zero]
      _ = ⟪G-coeffMulLpL A G,D⟫_ℝ := by rw [inner_sub_left,htestA,sub_zero]
  have hbound : ‖D‖^2 ≤ (delta*‖G‖)*‖D‖ := by
    calc
      ‖D‖^2 = ⟪D,D⟫_ℝ := (real_inner_self_eq_norm_sq D).symm
      _ = ⟪G-coeffMulLpL A G,D⟫_ℝ := he
      _ ≤ |⟪G-coeffMulLpL A G,D⟫_ℝ| := le_abs_self _
      _ ≤ ‖G-coeffMulLpL A G‖*‖D‖ := abs_real_inner_le_norm _ _
      _ ≤ (delta*‖G‖)*‖D‖ := mul_le_mul_of_nonneg_right
        (actual_coefficient_energy_difference_two A hdelta hA G) (norm_nonneg D)
  change ‖D‖ ≤ delta*‖G‖
  nlinarith [norm_nonneg D,mul_nonneg hdelta (norm_nonneg G)]

end PowerConvexity
