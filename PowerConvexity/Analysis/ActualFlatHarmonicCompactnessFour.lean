import PowerConvexity.Analysis.ActualFlatEllipticCompactnessFour
import PowerConvexity.Analysis.ActualMatrixHarmonicUniformLimitFour

/-! # Actual half-ball harmonic limits with the original zero flat boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_elliptic_harmonic_subsequence_four
    {N : E} (hN : ‖N‖=1)
    {lam Lambda Ka Kf F alpha : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (halpha : 0 < alpha)
    (A : ℕ → EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hlo : ∀ n, lam ≤ (A n).lam) (hhi : ∀ n, (A n).Λ ≤ Lambda)
    (hpos : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ((A n).a x).PosDef)
    (hreg : ∀ n i j, ContDiffOn ℝ 1 (fun x => (A n).a x i j) (actualFlatUpperBallFour N 1))
    (hdiv : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ∀ j,
      (∑ i, fderiv ℝ (fun y => (A n).a y i j) x (EuclideanSpace.single i 1)) = 0)
    (hhold : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      ∀ y, y ∈ actualFlatUpperBallFour N 1 →
      ‖actualMatrixOperatorTwo ((A n).a x)-actualMatrixOperatorTwo ((A n).a y)‖ ≤ Ka*‖x-y‖^alpha)
    (f u : ℕ → E → ℝ) (hfC : ∀ n, ContDiffOn ℝ 1 (f n) (actualFlatUpperBallFour N 1))
    (hfhold : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      ∀ y, y ∈ actualFlatUpperBallFour N 1 → |f n x-f n y| ≤ Kf*‖x-y‖^alpha)
    (hfb : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → |f n x| ≤ F)
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) (actualFlatUpperBallFour N 1))
    (huC : ∀ n, ContinuousOn (u n) (actualFlatClosedUpperBallFour N 1))
    (hu0 : ∀ n x, x ∈ closedBall (0 : E) 1 → inner ℝ N x=0 → u n x=0)
    (hub : ∀ n x, x ∈ actualFlatClosedUpperBallFour N 1 → |u n x| ≤ 1)
    (hpde : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      (∑ i, ∑ j, (A n).a x i j*euclideanHessian (u n) x i j) = -f n x)
    (haI : ∀ i j, TendstoUniformlyOn (fun n y => (A n).a y i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N 1))
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0))
    (hfsmall : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → |f n x| ≤ eps n) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (actualFlatClosedUpperBallFour N (1/2)) ∧
      InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) ∧
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/2), inner ℝ N x=0 → g x=0 := by
  obtain ⟨phi,hphi,g,hgc,hunif,hgb,hgd,hg0⟩ :=
    actual_flat_elliptic_uniform_subsequence_four hN hlam hLambda hKa hKf hF halpha
      A hlo hhi hpos hreg hdiv hhold f u hfC hfhold hfb hu huC hu0 hub hpde
  have hsub : actualFlatUpperBallFour N (1/2) ⊆ actualFlatUpperBallFour N 1 := fun x hx =>
    ⟨ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1) hx.1,hx.2⟩
  have hcl : actualFlatUpperBallFour N (1/2) ⊆ actualFlatClosedUpperBallFour N (1/2) := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hco (i j : Fin (2+2)) : TendstoUniformlyOn (fun n y => (A (phi n)).a y i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N (1/2)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro delta hd
    exact hphi.tendsto_atTop.eventually
      ((Metric.tendstoUniformlyOn_iff.mp ((haI i j).mono hsub)) delta hd)
  have hzero := heps.comp hphi.tendsto_atTop
  have hgH : InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) := by
    apply actual_matrix_uniform_limit_is_classical_harmonic_four
      (actualFlatUpperBallFour_isOpen N (1/2)) hco
      (fun n x hx => (hpos (phi n) x (hsub hx)).posSemidef) hzero
      (fun n => (hu (phi n)).mono hsub) ?_ (hgc.mono hcl) (hunif.mono hcl)
    intro n x hx
    rw [actual_matrix_contraction_euclideanHessian_four _
      ((hu (phi n)).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds (hsub hx))),
      hpde (phi n) x (hsub hx),abs_neg]
    exact hfsmall (phi n) x (hsub hx)
  exact ⟨phi,hphi,g,hgc,hunif,hgH,hgb,hg0⟩

end PowerConvexity
