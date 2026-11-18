import PowerConvexity.Analysis.ActualFlatDriftEllipticCompactnessFour
import PowerConvexity.Analysis.ActualScalarCoefficientNormalizationFour

/-! # The same actual half-ball equation at a fixed general ellipticity scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_general_drift_uniform_subsequence_four
    {N : E} (hN : ‖N‖=1)
    (A : ℕ → EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    {lam L B F : ℝ} (hlam : 0 < lam) (hlo : ∀ n, (A n).lam=lam)
    (hL : ∀ n, (A n).Λ ≤ L) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hsmall : (3*(4*(L/lam)+(F/lam)/4+1)+3)*(B/lam) ≤ 2)
    (hpos : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ((A n).a x).PosDef)
    (hA : ∀ n i j, ContDiffOn ℝ 1 (fun x => (A n).a x i j) (actualFlatUpperBallFour N 1))
    (b : ℕ → E → E) (hb : ∀ n, ContinuousOn (b n) (actualFlatUpperBallFour N 1))
    (hdiv : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → actualCoefficientColumnDivergenceFour (A n).a x=b n x)
    (hbb : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ‖b n x‖ ≤ B)
    (f u : ℕ → E → ℝ) (hf : ∀ n, ContinuousOn (f n) (actualFlatUpperBallFour N 1))
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) (actualFlatUpperBallFour N 1))
    (huC : ∀ n, ContinuousOn (u n) (actualFlatClosedUpperBallFour N 1))
    (hu0 : ∀ n x, x ∈ closedBall (0 : E) 1 → inner ℝ N x=0 → u n x=0)
    (hub : ∀ n x, x ∈ actualFlatClosedUpperBallFour N 1 → |u n x| ≤ 1)
    (hfb : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → |f n x| ≤ F)
    (hpde : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      (∑ i, ∑ j, (A n).a x i j*euclideanHessian (u n) x i j)+fderiv ℝ (u n) x (b n x) = -f n x) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (actualFlatClosedUpperBallFour N (1/2)) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) ∧
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/2), inner ℝ N x=0 → g x=0 := by
  let C := fun n => actualScalarNormalizedCoeffFour (A n)
  have hCa (n : ℕ) (x : E) : (C n).1.a x=lam⁻¹ • (A n).a x := by
    change (A n).lam⁻¹ • (A n).a x=lam⁻¹ • (A n).a x
    rw [hlo n]
  have hCL (n : ℕ) : (C n).1.Λ ≤ L/lam := by
    change (A n).Λ/(A n).lam ≤ L/lam
    rw [hlo n]
    exact div_le_div_of_nonneg_right (hL n) hlam.le
  have hCp (n : ℕ) (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) : ((C n).1.a x).PosDef := by
    rw [hCa]
    exact (hpos n x hx).smul (inv_pos.mpr hlam)
  have hCr (n : ℕ) (i j : Fin (2+2)) :
      ContDiffOn ℝ 1 (fun x => (C n).1.a x i j) (actualFlatUpperBallFour N 1) := by
    change ContDiffOn ℝ 1 (fun x => (A n).lam⁻¹*(A n).a x i j) _
    rw [hlo n]
    exact contDiffOn_const.mul (hA n i j)
  have hCd (n : ℕ) (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) :
      actualCoefficientColumnDivergenceFour (C n).1.a x=lam⁻¹ • b n x := by
    rw [actual_scalar_normalized_column_divergence_four (A n)
      (fun i j => ((hA n i j).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds hx)).differentiableAt (by norm_num)),
      hdiv n x hx,hlo n]
  have hbb' (n : ℕ) (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) :
      ‖lam⁻¹ • b n x‖ ≤ B/lam := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left (hbb n x hx) (inv_nonneg.mpr hlam.le)
  have hfb' (n : ℕ) (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) : |lam⁻¹*f n x| ≤ F/lam := by
    rw [abs_mul,abs_of_pos (inv_pos.mpr hlam)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left (hfb n x hx) (inv_nonneg.mpr hlam.le)
  have hpde' (n : ℕ) (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) :
      (∑ i, ∑ j, (C n).1.a x i j*euclideanHessian (u n) x i j)+
        fderiv ℝ (u n) x (lam⁻¹ • b n x) = -(lam⁻¹*f n x) := by
    simp only [hCa,Matrix.smul_apply,smul_eq_mul,map_smul]
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [← mul_add,hpde n x hx,mul_neg]
  obtain ⟨phi,hphi,g,hgc,hunif,hgb,_,hg0⟩ := actual_flat_drift_elliptic_uniform_subsequence_four hN
    C hCL (div_nonneg hB hlam.le) (div_nonneg hF hlam.le) hsmall hCp hCr
    (fun n x => lam⁻¹ • b n x) (fun n => (hb n).const_smul lam⁻¹) hCd hbb'
    (fun n x => lam⁻¹*f n x) u (fun n => continuousOn_const.mul (hf n)) hu huC hu0 hub hfb' hpde'
  exact ⟨phi,hphi,g,hgc,hunif,hgb,hg0⟩

end PowerConvexity
