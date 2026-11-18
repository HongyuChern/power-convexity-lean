import PowerConvexity.Analysis.ActualScalarWeakLocalizationTwo

/-! # Caccioppoli estimate for the actual scalar equation.
The admissible test is constructed as eta*(eta*u), with the two actual
Sobolev product gradients. The source term is the actual scalar integral.
No local gradient bound or regular representative is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_cutoff_energy_two {U : Set F} (hU : IsOpen U)
    (A : NormalizedEllipticCoeff (2+2) U) {f u eta : F → ℝ}
    (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A.1 f u)
    (uw : MemW1pWitness 2 u U)
    (he : ContDiff ℝ (⊤ : ℕ∞) eta) (hec : HasCompactSupport eta)
    (hes : tsupport eta ⊆ U) (heb : ∀ x, |eta x| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (heD : ∀ x, ‖fderiv ℝ eta x‖ ≤ C) :
    ∫ x in U, (eta x)^2*‖uw.weakGrad x‖^2 ≤
      (1+4*A.1.Λ^2*C^2)*(∫ x in U, (u x)^2)+(∫ x in U, (f x)^2) := by
  let ew := uw.mulSmoothBoundedP (by norm_num : (1 : ENNReal) ≤ 2) hU he
    (by norm_num : (0 : ℝ) ≤ 1) hC heb heD
  let tw := ew.mulSmoothBoundedP (by norm_num : (1 : ENNReal) ≤ 2) hU he
    (by norm_num : (0 : ℝ) ≤ 1) hC heb heD
  let phi : F → ℝ := fun x => eta x*(eta x*u x)
  have hp : MemH01 phi U := by
    have hs : tsupport phi ⊆ tsupport eta := tsupport_smul_subset_left eta (fun x => eta x*u x)
    have hc : HasCompactSupport phi := HasCompactSupport.intro' hec.isCompact (isClosed_tsupport eta)
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))
    have hm : MemW1p (ENNReal.ofReal (2 : ℝ)) phi U := by simpa using tw.memW1p
    simpa using memW01p_of_memW1p_of_tsupport_subset hU (by norm_num : (1 : ℝ) < 2)
      hm hc (hs.trans hes)
  have htest := hu.2 uw phi hp tw
  have hexpand (x : F) : bilinFormIntegrandOfCoeff A.1 uw tw x =
      (eta x)^2*bilinFormIntegrandOfCoeff A.1 uw uw x+
        2*eta x*u x*⟪matMulE (A.1.a x) (uw.weakGrad x),deGiorgiFderivVec eta x⟫_ℝ := by
    have h1 := bilinFormIntegrand_mul_smooth_eq hU A.1 uw ew he
      (by norm_num : (0 : ℝ) ≤ 1) hC heb heD (by norm_num : (1 : ENNReal) ≤ 2) x
    have h2 := bilinFormIntegrand_mul_smooth_eq hU A.1 uw uw he
      (by norm_num : (0 : ℝ) ≤ 1) hC heb heD (by norm_num : (1 : ENNReal) ≤ 2) x
    have hv : (WithLp.toLp 2 (fun i : Fin (2+2) =>
        (fderiv ℝ eta x) (EuclideanSpace.single i 1)) : F) = deGiorgiFderivVec eta x := by
      ext i
      simp only [PiLp.toLp_apply,deGiorgiFderivVec_apply]
    rw [hv] at h1 h2
    change bilinFormIntegrandOfCoeff A.1 uw tw x =
      eta x*bilinFormIntegrandOfCoeff A.1 uw ew x+
      (eta x*u x)*⟪matMulE (A.1.a x) (uw.weakGrad x),deGiorgiFderivVec eta x⟫_ℝ at h1
    change bilinFormIntegrandOfCoeff A.1 uw ew x =
      eta x*bilinFormIntegrandOfCoeff A.1 uw uw x+
      u x*⟪matMulE (A.1.a x) (uw.weakGrad x),deGiorgiFderivVec eta x⟫_ℝ at h2
    rw [h1,h2]
    ring
  have hgI : Integrable (fun x => ‖uw.weakGrad x‖^2) (volume.restrict U) :=
    uw.weakGrad_norm_memLp.integrable_sq
  have hwI : Integrable (fun x => (eta x)^2*‖uw.weakGrad x‖^2) (volume.restrict U) := by
    apply Integrable.mono' hgI
    · exact ((he.continuous.pow 2).aestronglyMeasurable.mul hgI.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun x => by
        have hh : (eta x)^2 ≤ 1 := by nlinarith [sq_abs (eta x),heb x,abs_nonneg (eta x)]
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖uw.weakGrad x‖])
  have hpt : ∀ᵐ x ∂volume.restrict U,
      (1/2 : ℝ)*(eta x)^2*‖uw.weakGrad x‖^2 ≤
        bilinFormIntegrandOfCoeff A.1 uw tw x+2*A.1.Λ^2*C^2*(u x)^2 := by
    filter_upwards [A.1.coercive,A.1.mixed_bound] with x hco hm
    have hco' : ‖uw.weakGrad x‖^2 ≤ bilinFormIntegrandOfCoeff A.1 uw uw x := by
      simpa only [A.2,one_mul,bilinFormIntegrandOfCoeff,real_inner_comm] using hco (uw.weakGrad x)
    have hi : |⟪matMulE (A.1.a x) (uw.weakGrad x),deGiorgiFderivVec eta x⟫_ℝ| ≤
        A.1.Λ*C*‖uw.weakGrad x‖ := by
      have hh := hm (uw.weakGrad x) (deGiorgiFderivVec eta x)
      rw [real_inner_comm,deGiorgi_norm_fderivVec_eq_norm_fderiv] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (heD x) A.1.Λ_nonneg) (norm_nonneg _))
    have hc : |2*eta x*u x*⟪matMulE (A.1.a x) (uw.weakGrad x),deGiorgiFderivVec eta x⟫_ℝ| ≤
        2*|eta x| * |u x| * (A.1.Λ*C*‖uw.weakGrad x‖) := by
      simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] using
        mul_le_mul_of_nonneg_left hi (abs_nonneg (2*eta x*u x))
    have hy : 2*|eta x| * |u x| * (A.1.Λ*C*‖uw.weakGrad x‖) ≤
        (1/2 : ℝ)*(eta x)^2*‖uw.weakGrad x‖^2+2*A.1.Λ^2*C^2*(u x)^2 := by
      have young (a b : ℝ) : 2*a*b ≤ (1/2 : ℝ)*a^2+2*b^2 := by
        nlinarith [sq_nonneg (a-2*b)]
      have hh := young (|eta x| * ‖uw.weakGrad x‖) (A.1.Λ*C*|u x|)
      simp only [mul_pow,sq_abs] at hh
      nlinarith only [hh]
    have hp0 := mul_le_mul_of_nonneg_left hco' (sq_nonneg (eta x))
    have hcross := neg_le_of_abs_le (hc.trans hy)
    rw [hexpand]
    linarith
  have hmain := integral_mono_ae (hwI.const_mul (1/2 : ℝ))
    ((integrable_bilinFormIntegrandOfCoeff A.1 uw tw).add
      (uw.memLp.integrable_sq.const_mul (2*A.1.Λ^2*C^2))) (by
        filter_upwards [hpt] with x hx
        change (1/2 : ℝ)*((eta x)^2*‖uw.weakGrad x‖^2) ≤
          bilinFormIntegrandOfCoeff A.1 uw tw x+(2*A.1.Λ^2*C^2)*(u x)^2
        simpa only [mul_assoc] using hx)
  simp only [Pi.add_apply] at hmain
  rw [integral_const_mul,integral_add (integrable_bilinFormIntegrandOfCoeff A.1 uw tw)
    (uw.memLp.integrable_sq.const_mul (2*A.1.Λ^2*C^2)),integral_const_mul] at hmain
  change (1/2 : ℝ)*(∫ x in U, (eta x)^2*‖uw.weakGrad x‖^2) ≤
    bilinFormOfCoeff A.1 uw tw+2*A.1.Λ^2*C^2*(∫ x in U, (u x)^2) at hmain
  rw [htest] at hmain
  have hload : (∫ x in U, f x*phi x) ≤
      (1/2 : ℝ)*((∫ x in U, (f x)^2)+(∫ x in U, (u x)^2)) := by
    have hpI := hf.integrable_mul tw.memLp
    have hI := ((hf.integrable_sq.add uw.memLp.integrable_sq).const_mul (1/2 : ℝ))
    have hh := integral_mono hpI hI (fun x => by
      have he2 : (eta x)^2 ≤ 1 := by nlinarith [sq_abs (eta x),heb x,abs_nonneg (eta x)]
      have hy : |f x*u x| ≤ ((f x)^2+(u x)^2)/2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|f x|-|u x|),sq_abs (f x),sq_abs (u x)]
      calc
        f x*phi x = (eta x)^2*(f x*u x) := by dsimp only [phi];ring
        _ ≤ (eta x)^2*|f x*u x| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ |f x*u x| := by nlinarith [abs_nonneg (f x*u x)]
        _ ≤ (1/2 : ℝ)*((f x)^2+(u x)^2) := by linarith)
    simp only [Pi.add_apply,Pi.mul_apply] at hh
    simpa only [phi,integral_const_mul,integral_add hf.integrable_sq uw.memLp.integrable_sq] using hh
  nlinarith

end PowerConvexity
