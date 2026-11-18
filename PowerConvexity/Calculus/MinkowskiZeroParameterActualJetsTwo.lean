import PowerConvexity.Calculus.MinkowskiZeroParameterActualHessianBoundTwo

/-! # Actual first and second jets at the ball endpoint.
The new proved actual common-ball Hessian estimate supplies the actual
isometric CMA criterion, with joint values obtained from actual zero extensions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
attribute [local instance] zphRealSpace zphRealModule zphDualSpace zphDualModule
  zphDualTopology zphHessSpace zphHessModule zphHessTopology
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_actual_jets_continuousAt_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho D : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hD : 0 ≤ D)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ D) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ D)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    ContinuousAt (fun p : I × E => fderiv ℝ (u p.1) p.2) ((⟨0,by norm_num⟩ : I),x) ∧
    ContinuousAt (fun p : I × E => realHessian (u p.1) p.2) ((⟨0,by norm_num⟩ : I),x) := by
  let t0 : I := ⟨0,by norm_num⟩
  obtain ⟨r,hr,M,hM,hbound⟩ := minkowski_actual_real_Hessian_bound_at_zero_two
    hA hconv e hab hR hrho hD hballA hballB hAb hBb hu hx
  obtain ⟨L,hLa,hLb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  have hLa' : (fun i => L (realDirections i)) = e := funext hLa
  have hLb' : (fun i => L (imagDirections i)) = (fun j => Complex.I • e j) := funext hLb
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have hV (t : I) : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball hAn t
  have hball0 : ball x (4*r) ⊆ minkowskiDomain t0 A (ball (0 : E) R) := hbound.self_of_nhds.1
  have hZ := hu.joint_continuous hab hA isOpen_ball hconv (convex_ball 0 R)
    hrho hD hballA hballB hAb hBb
  have hval (y : E) (hy : y ∈ closedBall x (3*r)) :
      ContinuousAt (fun p : I × E => u p.1 p.2) (t0,y) := by
    have hyV := hball0 ((closedBall_subset_ball (by linarith : 3*r < 4*r)) hy)
    apply hZ.continuousAt.congr_of_eventuallyEq
    filter_upwards [minkowskiDomain_joint_mem_nhds hconv (convex_ball 0 R)
      hrho hD hballA hballB hAb hBb (hV t0) hyV] with p hp
    simp only [Set.indicator_of_mem hp]
  apply realHessian_family_continuousAt_of_values_CMA_isometric_bound (by norm_num : 2≤2)
    L hr hM hval
  filter_upwards [hbound] with t ht
  rw [hLa',hLb']
  exact ⟨(hu t).1.mono ht.1,fun y hy => (hu t).2.2.2.1 y (ht.1 hy),
    fun y hy => (hu t).2.2.1 y (ht.1 hy),ht.2⟩

end PowerConvexity
