import PowerConvexity.Calculus.ActualContinuationC4CompactnessTwo
import PowerConvexity.Calculus.ContinuationInteriorHessianEquicontinuityTwo
import PowerConvexity.Calculus.ActualClosureC2JetLimitFromBoundaryTwo

/-! # Actual nonlinear continuation closedness from the common boundary Hessian estimate

All interior compactness, strict plurisubharmonicity and the nonconstant
density equation are inherited for the same constructed limit. The only
additional compactness hypothesis is the displayed common boundary estimate.
Its derivation from the original nonlinear data is not asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance acbcRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance acbcRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_actual_classical_limit_of_boundary_modulus_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {C delta gamma : ℝ} (hdelta : 0 < delta) (hgamma : 0 < gamma)
    (hboundary : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v →
      ∀ J : ClosureC2Jet v U, ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^gamma)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc (0 : ℝ) 1)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (hslim : Tendsto s atTop (𝓝 s₀))
    (hex : ∀ n, ∃ v : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) v) :
    ∃ g : E → ℝ, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s₀) g := by
  choose u hdata using hex
  have hjets (n : ℕ) : Nonempty (ClosureC2Jet (u n) U) := (hdata n).2.1
  let J : ∀ n, ClosureC2Jet (u n) U := fun n => Classical.choice (hjets n)
  obtain ⟨M,hM,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hgeometry e hab (hw.of_le (by norm_num)) hwb hwp hwd hf hfb hdef
  have hactual (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (v : E → ℝ)
      (hv : ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w r) v)
      (x : E) (hx : x ∈ U) : ‖fderiv ℝ v x‖ ≤ M ∧ ‖realHessian v x‖ ≤ M := by
    obtain ⟨Jv⟩ := hv.2.1
    simpa only [Jv.derivative_eq hx,Jv.hessian_eq hx,realHessian] using
      (hbound r hr v hv Jv x (subset_closure hx)).2
  obtain ⟨B,hcompact⟩ := continuation_density_sequence_C4_interior_compactness_two
    hU hconv hK hgeometry e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨phi,hphi,g,D,hg1,hg4,hgsol,hDc,hDcl,hDg,hgb,hval,hder,hLip,hgbound⟩ :=
    hcompact s hs s₀ hs₀ hslim u hdata J
  have hinner := continuation_density_closure_hessian_equicontinuousOn_interior_two
    hU hconv hK e hab (hw.of_le (by norm_num)) hwd hM hactual
    (fun n => s (phi n)) (fun n => hs (phi n)) (fun n => u (phi n))
    (fun n => hdata (phi n)) (fun n => J (phi n))
  obtain ⟨hg2,psi,hpsi,Jg,hJg,hHlim,hHg⟩ :=
    actual_closure_C2_jet_limit_of_boundary_hessian_modulus hU hK
      (fun n => u (phi n)) (fun n => (hdata (phi n)).1.of_le (by norm_num))
      (fun n => J (phi n)) hg1.continuousOn hDc hDg
      (fun x hx => hder.tendsto_at (subset_closure hx))
      (fun n x hx => (hbound (s (phi n)) (hs (phi n)) (u (phi n))
        (hdata (phi n)) (J (phi n)) x hx).2.2)
      hinner hdelta hgamma
      (fun n c hc x hx hnear => hboundary (s (phi n)) (hs (phi n)) (u (phi n))
        (hdata (phi n)) (J (phi n)) c hc x hx hnear)
  exact ⟨g,hg4,⟨Jg⟩,fun x hx => (hgsol x hx).1,fun x hx => (hgsol x hx).2,hgb⟩

end PowerConvexity
