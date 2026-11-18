import PowerConvexity.Analysis.ActualUniformPrescribedHolderSchauderTwo

/-! # The same actual weak solution solves the classical equation for Holder loads

There is no approximation in the Holder norm. The actual frozen polynomial
field retains the equation and identifies the derivatives of the given
continuous weak representative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuous_holder_local_classical_two
    {rho lam Lambda Ka Kf F N₀ alpha : ℝ}
    (hrho : 0 < rho) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hN₀ : 0 ≤ N₀)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    {x₀ : E} {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hclosed : closedBall x₀ rho ⊆ U)
    (A : EllipticCoeff (2+2) U) (hlo : lam ≤ A.lam) (hhi : A.Λ ≤ Lambda)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    (hhold : ∀ x ∈ closedBall x₀ rho, ∀ y ∈ closedBall x₀ rho,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U)) (hfC : ContinuousOn f U)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha)
    (hbound : ∀ x ∈ U, |f x| ≤ F) (huC : ContinuousOn u U)
    (hu : ActualScalarWeakEquationTwo A f u)
    (uw : MemW1pWitness 2 u U) (hun : ‖uw.memLp.toLp u‖ ≤ N₀) :
    ContDiffOn ℝ 2 u (ball x₀ (rho/4)) ∧
    ∀ x ∈ ball x₀ (rho/4),
      (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j) = -f x := by
  classical
  obtain ⟨R,hR,C,hC,theta,htheta,hthetab,hthetaalpha,happrox⟩ :=
    actual_uniform_prescribed_holder_physical_expansion_two hrho hlam hLambda
      hKa hKf hF hN₀ halpha halpha1
  have htheta1 : theta < 1 := by linarith
  let V := ball x₀ (rho/4)
  have hVU : V ⊆ U := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith : rho/4 ≤ rho))).trans hclosed
  have hdata := happrox x₀ U hU hUb hclosed A hlo hhi hpos hreg hdiv hhold
    f u hf hfC hLip hbound hu uw hun
  have hex : ∀ x : E, ∃ p : E → ℝ, x ∈ V →
      IsQuadraticPolynomial p ∧
      (∑ i, ∑ j, A.a x i j*euclideanHessian p x i j) = -f x ∧
      ∀ n : ℕ, (∫ y in ball x (R*theta^n), (u y-p y)^2) ≤
        C*((theta^alpha)^n)^2*(R*theta^n)^8 := by
    intro x
    by_cases hx : x ∈ V
    · obtain ⟨p,hp,hpde,herr⟩ := (hdata x hx).2
      exact ⟨p,fun _ => ⟨hp,hpde,herr⟩⟩
    · exact ⟨fun _ => 0,fun h => (hx h).elim⟩
  choose P hP using hex
  have hballs : ∀ x ∈ V, ball x R ⊆ U := fun x hx => (hdata x hx).1
  have herrHalf : ∀ x ∈ V, ∀ n : ℕ,
      (∫ y in ball x (R*theta^n), (u y-P x y)^2) ≤
        C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
    intro x hx n
    apply ((hP x hx).2.2 n).trans
    have hp : (theta^alpha)^n ≤ (1/2 : ℝ)^n :=
      pow_le_pow_left₀ (Real.rpow_nonneg htheta.le _) hthetaalpha n
    have hpsq : ((theta^alpha)^n)^2 ≤ ((1/2 : ℝ)^n)^2 :=
      (sq_le_sq₀ (pow_nonneg (Real.rpow_nonneg htheta.le _) n)
        (pow_nonneg (by norm_num) n)).mpr hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsq hC)
      (pow_nonneg (mul_nonneg hR.le (pow_nonneg htheta.le n)) 8)
  have hfield := actual_continuous_polynomial_field_jets_identify_two isOpen_ball isBounded_ball
    hVU uw.memLp (huC.mono hVU) P (fun x hx => (hP x hx).1)
    hR htheta htheta1 hC hballs herrHalf
  refine ⟨hfield.1,?_⟩
  intro x hx
  simpa only [euclideanHessian,(hfield.2 x hx).2.2] using (hP x hx).2.1


theorem actual_continuous_holder_classical_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {Ka Kf F alpha : ℝ} (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hhold : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U)) (hfC : ContinuousOn f U)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ Kf*‖x-y‖^alpha)
    (hbound : ∀ x ∈ U, |f x| ≤ F) (huC : ContinuousOn u U)
    (hu : ActualScalarWeakEquationTwo A f u) :
    ContDiffOn ℝ 2 u U ∧ ∀ x ∈ U,
      (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j) = -f x := by
  let uw := MemW1p.someWitness hu.1
  have hlocal : ∀ x ∈ U, ∃ rho > 0,
      ContDiffOn ℝ 2 u (ball x rho) ∧
      ∀ y ∈ ball x rho, (∑ i, ∑ j, A.a y i j*euclideanHessian u y i j) = -f y := by
    intro x hx
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
    have hclosed : closedBall x (r/2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    obtain ⟨hC,hPDE⟩ := actual_continuous_holder_local_classical_two (half_pos hr) A.hlam A.Λ_pos
      hKa hKf hF (norm_nonneg (uw.memLp.toLp u)) halpha halpha1 hU hUb hclosed A le_rfl le_rfl
      hpos hreg hdiv (fun z hz w hw => hhold z (hclosed hz) w (hclosed hw))
      hf hfC hLip hbound huC hu uw le_rfl
    exact ⟨(r/2)/4,by positivity,hC,hPDE⟩
  constructor
  · intro x hx
    obtain ⟨r,hr,hC,hPDE⟩ := hlocal x hx
    exact (hC.contDiffAt (ball_mem_nhds x hr)).contDiffWithinAt
  · intro x hx
    obtain ⟨r,hr,hC,hPDE⟩ := hlocal x hx
    exact hPDE x (mem_ball_self hr)

end PowerConvexity
