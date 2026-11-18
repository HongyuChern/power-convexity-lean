import PowerConvexity.Analysis.ActualFlatBoundaryCompactnessFour
import PowerConvexity.Analysis.ActualUniformClassicalLocalBoundFour
import PowerConvexity.Analysis.ActualFlatMatrixStripFour

/-! # Uniform boundary compactness of the actual elliptic half-ball family
The local control is derived from the original uniform scalar estimates,
and the boundary control from the actual matrix barrier on the same domain.
-/
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

theorem actual_matrix_contraction_euclideanHessian_four
    (C : Mat) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ)) C (realHessian u x) =
      ∑ i, ∑ j, C i j*euclideanHessian u x i j := by
  simp only [matrixHessianContraction,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change C i j*realHessian u x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
    C i j*realHessian u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [realHessian_symm hu]

theorem actual_flat_normal_pos_of_close_four {N x y : E} (hN : ‖N‖=1)
    (hxy : dist y x < inner ℝ N x) : 0 < inner ℝ N y := by
  have hh := real_inner_le_norm N (x-y)
  rw [hN,one_mul,inner_sub_right,← dist_eq_norm,dist_comm x y] at hh
  linarith

theorem actual_flat_elliptic_uniform_subsequence_four
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
      (∑ i, ∑ j, (A n).a x i j*euclideanHessian (u n) x i j) = -f n x) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (actualFlatClosedUpperBallFour N (1/2)) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) ∧
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2),
        |g x| ≤ (2*((4*Lambda+F/4+1)/lam+2))*inner ℝ N x) ∧
      ∀ x ∈ actualFlatClosedUpperBallFour N (1/2), inner ℝ N x=0 → g x=0 := by
  let U := actualFlatUpperBallFour N 1
  let K := actualFlatClosedUpperBallFour N (1/2)
  have hU : IsOpen U := actualFlatUpperBallFour_isOpen N 1
  have hK : IsCompact K := (isCompact_closedBall (0 : E) (1/2)).inter_right
    (isClosed_le continuous_const (innerSL ℝ N).continuous)
  have hKC : K ⊆ actualFlatClosedUpperBallFour N 1 := fun x hx =>
    ⟨closedBall_subset_closedBall (by norm_num : (1/2 : ℝ) ≤ 1) hx.1,hx.2⟩
  have hUC : U ⊆ actualFlatClosedUpperBallFour N 1 := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hKUpos (x : E) (hx : x ∈ K) (hn : 0 < inner ℝ N x) : x ∈ U :=
    ⟨closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1) hx.1,hn⟩
  have hlocal := actual_uniform_classical_local_Lipschitz_four hU hlam hLambda hKa hKf hF halpha
    A hlo hhi hpos hreg hdiv hhold f u hfC hfhold hfb hu
    (fun n x hx => hub n x (hUC hx)) hpde
  let B := 2*((4*Lambda+F/4+1)/lam+2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hbound (n : ℕ) (x : E) (hx : x ∈ K) : |u n x| ≤ B*inner ℝ N x := by
    have hLbound (y : E) (hy : y ∈ U) :
        |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
          ((A n).a y) (realHessian (u n) y)| ≤ F := by
      rw [actual_matrix_contraction_euclideanHessian_four _ ((hu n).contDiffAt (hU.mem_nhds hy)),
        hpde n y hy,abs_neg]
      exact hfb n y hy
    have hh := actual_flat_matrix_elliptic_boundary_strip_bound_four hN (A n)
      (fun i j => (hreg n i j).continuousOn) (hpos n) hF (huC n) (hu n) hLbound (hu0 n) (hub n) x hx
    have hnum : 0 ≤ 4*Lambda+F/4+1 := by positivity
    have hd : (4*(A n).Λ+F/4+1)/(A n).lam ≤ (4*Lambda+F/4+1)/lam := by
      calc
        _ ≤ (4*Lambda+F/4+1)/(A n).lam :=
          div_le_div_of_nonneg_right (by linarith [hhi n]) (A n).hlam.le
        _ ≤ _ := div_le_div_of_nonneg_left hnum hlam (hlo n)
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hx.2)
  apply actual_flat_compact_uniform_subsequence_four hN hK (fun x hx => hx.2) u
    (fun n => (huC n).mono hKC) hB (fun n x hx => hub n x (hKC hx)) hbound
  intro x hx hxpos
  obtain ⟨r,hr,C,hC,hmod⟩ := hlocal x (hKUpos x hx hxpos)
  refine ⟨min r (inner ℝ N x),lt_min hr hxpos,C,hC,?_⟩
  intro n y hy hxy
  have hypos := actual_flat_normal_pos_of_close_four hN (hxy.trans_le (min_le_right _ _))
  exact hmod n y (hKUpos y hy hypos) (hxy.trans_le (min_le_left _ _))

end PowerConvexity
