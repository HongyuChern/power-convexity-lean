import PowerConvexity.Analysis.ActualFlatGeneralDriftCompactnessFour
import PowerConvexity.Analysis.ActualDriftHarmonicUniformLimitFour

/-! # Actual harmonic limits on the same closed half-ball with vanishing drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_harmonic_subsequence_four
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
      (∑ i, ∑ j, (A n).a x i j*euclideanHessian (u n) x i j)+fderiv ℝ (u n) x (b n x) = -f n x)
    (haI : ∀ i j, TendstoUniformlyOn (fun n y => (A n).a y i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N 1))
    (hbzero : TendstoUniformlyOn b (fun _ => 0) atTop (actualFlatUpperBallFour N 1))
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0))
    (hfsmall : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → |f n x| ≤ eps n) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (actualFlatClosedUpperBallFour N (1/2)) ∧
      InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) ∧
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/2), inner ℝ N x=0 → g x=0 := by
  obtain ⟨phi,hphi,g,hgc,hunif,hgb,hg0⟩ := actual_flat_general_drift_uniform_subsequence_four
    hN A hlam hlo hL hB hF hsmall hpos hA b hb hdiv hbb f u hf hu huC hu0 hub hfb hpde
  have hsub : actualFlatUpperBallFour N (1/2) ⊆ actualFlatUpperBallFour N 1 := fun x hx =>
    ⟨ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1) hx.1,hx.2⟩
  have hcl : actualFlatUpperBallFour N (1/2) ⊆ actualFlatClosedUpperBallFour N (1/2) := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hco (i j : Fin (2+2)) : TendstoUniformlyOn (fun n y => (A (phi n)).a y i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N (1/2)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro delta hd
    exact hphi.tendsto_atTop.eventually ((Metric.tendstoUniformlyOn_iff.mp ((haI i j).mono hsub)) delta hd)
  have hbo : TendstoUniformlyOn (fun n => b (phi n)) (fun _ => 0) atTop (actualFlatUpperBallFour N (1/2)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro delta hd
    exact hphi.tendsto_atTop.eventually ((Metric.tendstoUniformlyOn_iff.mp (hbzero.mono hsub)) delta hd)
  have hgH : InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) := by
    apply actual_drift_uniform_limit_is_classical_harmonic_four
      (actualFlatUpperBallFour_isOpen N (1/2)) hco hbo
      (fun n x hx => (hpos (phi n) x (hsub hx)).posSemidef) (heps.comp hphi.tendsto_atTop)
      (fun n => (hu (phi n)).mono hsub) ?_ (hgc.mono hcl) (hunif.mono hcl)
    intro n x hx
    rw [actual_matrix_contraction_euclideanHessian_four _
      ((hu (phi n)).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds (hsub hx))),
      hpde (phi n) x (hsub hx),abs_neg]
    exact hfsmall (phi n) x (hsub hx)
  exact ⟨phi,hphi,g,hgc,hunif,hgH,hgb,hg0⟩

end PowerConvexity
