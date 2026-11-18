import PowerConvexity.Analysis.ActualFlatMatrixBoundaryBoundFour
import PowerConvexity.Analysis.ActualLaplacianWeakTestsTwo
import PowerConvexity.Analysis.UniformLimitStrictContacts

/-! # Actual matrix equations at moving strict contacts of a uniform limit
The coefficient entries converge to the identity on the same actual set.
Only the fixed test function is differentiated in the limit passage.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_scalar_constant_at_moving_points_four
    {U : Set E} {a : ℕ → E → ℝ} {c : ℝ}
    (ha : TendstoUniformlyOn a (fun _ => c) atTop U)
    {z : ℕ → E} (hz : ∀ n, z n ∈ U) :
    Tendsto (fun n => a n (z n)) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp ha) eps heps)
  exact ⟨N,fun n hn => by simpa only [dist_comm] using hN n hn (z n) (hz n)⟩

theorem actual_matrix_hessian_contraction_limit_four
    {C : ℕ → Mat} (hC : ∀ i j, Tendsto (fun n => C n i j) atTop (𝓝 ((1 : Mat) i j)))
    {p : E → ℝ} {x : E} (hp : ContDiffAt ℝ 2 p x)
    {z : ℕ → E} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
      (C n) (realHessian p (z n))) atTop
      (𝓝 ((realBlockHessian realDirections imagDirections p x).trace)) := by
  have hH : ContinuousAt (realHessian p) x :=
    ((hp.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hh (i j : Fin (2+2)) : Tendsto
      (fun n => realHessian p (z n) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) atTop
      (𝓝 (realHessian p x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1))) :=
    ((hH.clm_apply continuousAt_const).clm_apply continuousAt_const).tendsto.comp hz
  have ht := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => (hC i j).mul (hh i j)))
  have he : (∑ i, ∑ j, (1 : Mat) i j*
      realHessian p x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) =
      (realBlockHessian realDirections imagDirections p x).trace := by
    simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    exact actual_euclidean_trace_eq_block_trace_two p x
  rw [he] at ht
  exact ht

theorem actual_matrix_uniform_limit_strict_lower_test_four
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g p : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y)| ≤ F n)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn u g atTop K)
    (hstrict : ∀ y ∈ K, y ≠ x → g x-p x < g y-p y) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 0 := by
  let f : ℕ → E → ℝ := fun n y => u n y-p y
  have hfc (n : ℕ) : ContinuousOn (f n) K :=
    ((hu n).continuousOn.mono hKU).sub (hp.continuousOn.mono hKU)
  have hgc : ContinuousOn (fun y => g y-p y) K := hg.sub (hp.continuousOn.mono hKU)
  have hconv' : TendstoUniformlyOn f (fun y => g y-p y) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) eps heps] with n hn y hy
    simpa only [f,dist_sub_right] using hn y hy
  obtain ⟨z,hzK,hz⟩ := compact_strict_minimizer_stability hK (interior_subset hx)
    f (fun y => g y-p y) hfc hgc hconv' hstrict
  have hzU (n : ℕ) : z n ∈ U := hKU (hzK n).1
  have hreg (n : ℕ) : ContDiffAt ℝ 2 (u n) (z n) := (hu n).contDiffAt (hU.mem_nhds (hzU n))
  have hpreg (n : ℕ) : ContDiffAt ℝ 2 p (z n) := hp.contDiffAt (hU.mem_nhds (hzU n))
  have hcoeff (i j : Fin (2+2)) : Tendsto (fun n => a n (z n) i j) atTop (𝓝 ((1 : Mat) i j)) :=
    actual_uniform_scalar_constant_at_moving_points_four (ha i j) hzU
  have hlim := actual_matrix_hessian_contraction_limit_four hcoeff
    (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx)))) hz
  apply le_of_tendsto_of_tendsto hlim hF
  filter_upwards [hz (isOpen_interior.mem_nhds hx)] with n hn
  have hm : IsLocalMin (fun y => u n y-p y) (z n) :=
    (hzK n).2.isLocalMin (mem_interior_iff_mem_nhds.mp hn)
  have hH := realHessian_le_of_isLocalMin_sub (hreg n) (hpreg n) hm
  have hLP := matrixHessianContraction_positive
    (fun i => EuclideanSpace.single i (1 : ℝ)) (hpos n (z n) (hzU n))
  have hnonneg := hLP (realHessian (u n) (z n)-realHessian p (z n)) (by
    intro v
    simpa only [_root_.sub_apply] using sub_nonneg.mpr (hH v))
  simp only [matrixHessianContraction,LinearMap.coe_mk,AddHom.coe_mk,
    _root_.sub_apply,mul_sub,Finset.sum_sub_distrib] at hnonneg
  change 0 ≤ matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
    (a n (z n)) (realHessian (u n) (z n))-
    matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
    (a n (z n)) (realHessian p (z n)) at hnonneg
  linarith [(abs_le.mp (hLu n (z n) (hzU n))).2]

end PowerConvexity
