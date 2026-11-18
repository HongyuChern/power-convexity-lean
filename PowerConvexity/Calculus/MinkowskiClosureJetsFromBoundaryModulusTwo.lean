import PowerConvexity.Analysis.ActualMovingBoundaryModulusContinuity
import PowerConvexity.Calculus.MinkowskiAllParameterActualJetsTwo
import PowerConvexity.Calculus.ClosureJetContDiff

/-! # Actual moving closure jets from one common boundary Hessian modulus

Interior joint continuity is the proved actual CMA estimate, including the
ball endpoint.  The common boundary Hessian modulus supplies joint closure
Hessian continuity by the moving-domain transfer.  Compactness then gives
one global Hessian bound, hence a common spatial Lipschitz bound for the
actual closure derivatives.  The same transfer gives joint derivative
continuity.  Values use only genuine Dirichlet comparison and zero trace.

The only added analytic input here is the explicitly stated common boundary
Hessian Holder estimate for the same actual family and the same closure jets.
Neither that estimate nor existence of the family is asserted in this file.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E] [Nontrivial E]
attribute [local instance] zphRealSpace zphRealModule zphDualSpace zphDualModule
  zphDualTopology zphHessSpace zphHessModule zphHessTopology
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_joint_closure_jets_from_boundary_hessian_holder_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho L : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ L)
    {u : I → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R)))
    {C gamma radius : ℝ} (hgamma : 0 < gamma) (hradius : 0 < radius)
    (hholder : ∀ t : I, ∀ c ∈ frontier (minkowskiDomain t A (ball 0 R)),
      ∀ z ∈ closure (minkowskiDomain t A (ball 0 R)), ‖z-c‖ < radius →
        ‖(J t).hessian z-(J t).hessian c‖ ≤ C*‖z-c‖^gamma) :
    let K := {p : I × E | p.2 ∈ closure (minkowskiDomain p.1 A (ball 0 R))}
    ContinuousOn (fun p : I × E => u p.1 p.2) K ∧
    ContinuousOn (fun p : I × E => (J p.1).derivative p.2) K ∧
    ContinuousOn (fun p : I × E => (J p.1).hessian p.2) K := by
  let V : I → Set E := fun t => minkowskiDomain t A (ball (0 : E) R)
  let K := {p : I × E | p.2 ∈ closure (V p.1)}
  have hV (t : I) : IsOpen (V t) :=
    minkowskiDomain_isOpen hA isOpen_ball ⟨0,hballA (mem_closedBall_self hrho.le)⟩ t
  have hVc (t : I) : Convex ℝ (V t) := minkowskiDomain_convex hconv (convex_ball 0 R) t
  have hgraph : IsOpen {p : I × E | p.2 ∈ V p.1} :=
    minkowskiDomain_parameterGraph_isOpen hA isOpen_ball hconv (convex_ball 0 R)
      hrho hL hballA hballB hAb hBb
  have hKB : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hKG : IsCompact K := minkowskiDomain_closure_parameterGraph_isCompact hK hKB
  have hjoint (s : I) (x : E) (hx : x ∈ V s) :=
    minkowski_family_actual_jets_continuousAt_two hA hconv hK hboundary e hab
      hR hrho hL hballA hballB hAb hBb hu J hx
  have hHinterior (s : I) (x : E) (hx : x ∈ V s) :
      ContinuousAt (fun p : I × E => (J p.1).hessian p.2) (s,x) := by
    apply (hjoint s x hx).2.congr_of_eventuallyEq
    filter_upwards [hgraph.mem_nhds (show (s,x) ∈ {p : I × E | p.2 ∈ V p.1} from hx)] with p hp
    exact (J p.1).hessian_eq hp
  have hHjoint : ContinuousOn (fun p : I × E => (J p.1).hessian p.2) K := by
    apply actual_moving_closure_continuousOn_of_uniform_boundary_holder
      (F := fun t => (J t).hessian) (C := C)
      hV hVc hgraph hKG.isClosed hHinterior hgamma hradius
    intro t c hc z hz hdist
    simpa only [dist_eq_norm] using hholder t c hc z hz (by simpa only [dist_eq_norm] using hdist)
  obtain ⟨M,hM⟩ := (hKG.image_of_continuousOn hHjoint).isBounded.exists_norm_le
  let B : NNReal := ⟨max M 0,le_max_right _ _⟩
  have hHbound (t : I) (z : E) (hz : z ∈ closure (V t)) : ‖(J t).hessian z‖ ≤ (B : ℝ) :=
    (hM _ (mem_image_of_mem _ (show (t,z) ∈ K from hz))).trans (le_max_left _ _)
  have hDlip (t : I) : LipschitzOnWith B (J t).derivative (closure (V t)) := by
    apply (hVc t).closure.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => closureJet_derivative_hasFDerivWithinAt (hV t) (hVc t)
        ((hu t).1.of_le (by norm_num)) (J t) hx)
    intro x hx
    exact_mod_cast hHbound t x hx
  have hDinterior (s : I) (x : E) (hx : x ∈ V s) :
      ContinuousAt (fun p : I × E => (J p.1).derivative p.2) (s,x) := by
    apply (hjoint s x hx).1.congr_of_eventuallyEq
    filter_upwards [hgraph.mem_nhds (show (s,x) ∈ {p : I × E | p.2 ∈ V p.1} from hx)] with p hp
    exact (J p.1).derivative_eq hp
  have hDjoint : ContinuousOn (fun p : I × E => (J p.1).derivative p.2) K := by
    apply actual_moving_closure_continuousOn_of_uniform_boundary_holder
      (F := fun t => (J t).derivative)
      hV hVc hgraph hKG.isClosed hDinterior (C := (B : ℝ))
      (gamma := 1) (radius := 1) (by norm_num) (by norm_num)
    intro t c hc z hz _
    simpa only [Real.rpow_one] using
      (hDlip t).dist_le_mul z hz c (frontier_subset_closure hc)
  have hval : ContinuousOn (fun p : I × E => u p.1 p.2) K := by
    apply (hu.joint_continuous hab hA isOpen_ball hconv (convex_ball 0 R)
      hrho hL hballA hballB hAb hBb).continuousOn.congr
    intro p hp
    change u p.1 p.2 = (V p.1).indicator (u p.1) p.2
    by_cases hx : p.2 ∈ V p.1
    · simp only [Set.indicator_of_mem hx]
    · have hxf : p.2 ∈ frontier (V p.1) := by
        rw [(hV p.1).frontier_eq]
        exact ⟨hp,hx⟩
      rw [Set.indicator_of_notMem hx,(hu p.1).2.2.2.2 p.2 hxf]
  exact ⟨hval,hDjoint,hHjoint⟩

end PowerConvexity
