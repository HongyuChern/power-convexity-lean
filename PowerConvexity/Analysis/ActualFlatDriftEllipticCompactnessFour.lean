import PowerConvexity.Analysis.ActualUniformLocalDriftModulusFour
import PowerConvexity.Analysis.ActualFlatDriftMatrixStripFour
import PowerConvexity.Analysis.ActualFlatLocalModulusCompactnessFour
import PowerConvexity.Analysis.ActualFlatEllipticCompactnessFour

/-! # Actual closed half-ball compactness retaining the chart drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_elliptic_uniform_subsequence_four
    {N : E} (hN : ‖N‖=1)
    (A : ℕ → NormalizedEllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    {L B F : ℝ} (hL : ∀ n, (A n).1.Λ ≤ L) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hsmall : (3*(4*L+F/4+1)+3)*B ≤ 2)
    (hpos : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ((A n).1.a x).PosDef)
    (hA : ∀ n i j, ContDiffOn ℝ 1 (fun x => (A n).1.a x i j) (actualFlatUpperBallFour N 1))
    (b : ℕ → E → E) (hb : ∀ n, ContinuousOn (b n) (actualFlatUpperBallFour N 1))
    (hdiv : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      actualCoefficientColumnDivergenceFour (A n).1.a x=b n x)
    (hbb : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → ‖b n x‖ ≤ B)
    (f u : ℕ → E → ℝ) (hf : ∀ n, ContinuousOn (f n) (actualFlatUpperBallFour N 1))
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) (actualFlatUpperBallFour N 1))
    (huC : ∀ n, ContinuousOn (u n) (actualFlatClosedUpperBallFour N 1))
    (hu0 : ∀ n x, x ∈ closedBall (0 : E) 1 → inner ℝ N x=0 → u n x=0)
    (hub : ∀ n x, x ∈ actualFlatClosedUpperBallFour N 1 → |u n x| ≤ 1)
    (hfb : ∀ n x, x ∈ actualFlatUpperBallFour N 1 → |f n x| ≤ F)
    (hpde : ∀ n x, x ∈ actualFlatUpperBallFour N 1 →
      (∑ i, ∑ j, (A n).1.a x i j*euclideanHessian (u n) x i j)+fderiv ℝ (u n) x (b n x) = -f n x) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (actualFlatClosedUpperBallFour N (1/2)) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ (2*(4*L+F/4+1+2))*inner ℝ N x) ∧
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/2), inner ℝ N x=0 → g x=0 := by
  let U := actualFlatUpperBallFour N 1
  let K := actualFlatClosedUpperBallFour N (1/2)
  have hU : IsOpen U := actualFlatUpperBallFour_isOpen N 1
  have hK : IsCompact K := (isCompact_closedBall (0 : E) (1/2)).inter_right
    (isClosed_le continuous_const (innerSL ℝ N).continuous)
  have hKC : K ⊆ actualFlatClosedUpperBallFour N 1 := fun x hx =>
    ⟨closedBall_subset_closedBall (by norm_num : (1/2 : ℝ) ≤ 1) hx.1,hx.2⟩
  have hUC : U ⊆ actualFlatClosedUpperBallFour N 1 := fun x hx => ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hKU (x : E) (hx : x ∈ K) (hn : 0 < inner ℝ N x) : x ∈ U :=
    ⟨closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1) hx.1,hn⟩
  have hL0 : 0 ≤ L := (A 0).1.Λ_nonneg.trans (hL 0)
  have htrace (n : ℕ) (x : E) (hx : x ∈ U) : 1 ≤ ((A n).1.a x).trace := by
    have hh := actual_elliptic_matrix_trace_lower_four hU (A n).1
      (fun i j => (hA n i j).continuousOn) x hx
    rw [(A n).property,mul_one] at hh
    linarith
  have hlocal := actual_uniform_classical_local_drift_modulus_four hU A hL
    (by norm_num : (0 : ℝ) ≤ 1) hB hF hA b hb hdiv htrace hbb f u hf hu
    (fun n x hx => hub n x (hUC hx)) hfb hpde
  let C := 2*(4*L+F/4+1+2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound (n : ℕ) (x : E) (hx : x ∈ K) : |u n x| ≤ C*inner ℝ N x := by
    have hbs (y : E) (hy : y ∈ U) :
        (3*((4*(A n).1.Λ+F/4+1)/(A n).1.lam)+3)*‖b n y‖ ≤ 2 := by
      rw [(A n).property,div_one]
      have hh : 3*(4*(A n).1.Λ+F/4+1)+3 ≤ 3*(4*L+F/4+1)+3 := by linarith [hL n]
      exact (mul_le_mul hh (hbb n y hy) (norm_nonneg _) (by positivity)).trans hsmall
    have hLu (y : E) (hy : y ∈ U) :
        |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
          ((A n).1.a y) (realHessian (u n) y)+fderiv ℝ (u n) y (b n y)| ≤ F := by
      rw [actual_matrix_contraction_euclideanHessian_four _ ((hu n).contDiffAt (hU.mem_nhds hy)),
        hpde n y hy,abs_neg]
      exact hfb n y hy
    have hh := actual_flat_drift_matrix_boundary_strip_four hN (A n).1
      (fun i j => (hA n i j).continuousOn) (hpos n) hF (b n) hbs (huC n) (hu n) hLu (hu0 n) (hub n) x hx
    rw [(A n).property,div_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith [hL n]) hx.2)
  apply actual_flat_compact_uniform_subsequence_of_local_modulus_four hN hK
    (fun x hx => hx.2) u (fun n => (huC n).mono hKC) hC
    (fun n x hx => hub n x (hKC hx)) hbound
  intro x hx hxpos eps heps
  obtain ⟨r,hr,hmod⟩ := hlocal x (hKU x hx hxpos) eps heps
  refine ⟨min r (inner ℝ N x),lt_min hr hxpos,?_⟩
  intro n y hy hxy
  have hypos := actual_flat_normal_pos_of_close_four hN (hxy.trans_le (min_le_right _ _))
  exact hmod n y (hKU y hy hypos) (hxy.trans_le (min_le_left _ _))

end PowerConvexity
