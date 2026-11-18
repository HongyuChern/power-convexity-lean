import PowerConvexity.Calculus.ClassicalBoundaryNormalTwo
import PowerConvexity.Calculus.ClosureStrictBranch
import PowerConvexity.Calculus.FrameDualQuadratics

/-! # The strict complex tangential form of the actual boundary jet

The closure Hessian is paired on arbitrary real directions v and I v.
The result concerns the genuine closure jet of the given solution. Identifying
this jet with the Levi form of an independently chosen smooth defining
function, and constructing the parallel-domain normal map, are separate steps.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem closure_complexField_complexFrame_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (a b : Fin 2 → E) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    {x : E} (hx : x ∈ closure U) :
    J.complexField (complexFrameReal Q a b) (complexFrameImag Q a b) x =
      Q * J.complexField a b x * Q.conjTranspose := by
  have he : EqOn
      (J.complexField (complexFrameReal Q a b) (complexFrameImag Q a b))
      (fun y => Q * J.complexField a b y * Q.conjTranspose) U := by
    intro y hy
    change J.complexField (complexFrameReal Q a b) (complexFrameImag Q a b) y =
      Q * J.complexField a b y * Q.conjTranspose
    rw [closure_complexField_eq_interior J hy (hu.contDiffAt (hU.mem_nhds hy)),
      closure_complexField_eq_interior J hy (hu.contDiffAt (hU.mem_nhds hy))]
    exact complexHessian_complexFrame (hu.contDiffAt (hU.mem_nhds hy)) Q a b
  have hc : ContinuousOn (fun y => Q * J.complexField a b y * Q.conjTranspose) (closure U) :=
    by
      have hA := J.continuousOn_complexField a b
      fun_prop
  exact he.of_subset_closure (J.continuousOn_complexField _ _) hc subset_closure Subset.rfl hx

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem closure_complexField_posDef_paired_hessian_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (e : Module.Basis (Fin 2) ℂ E)
    {x : E} (hx : x ∈ closure U)
    (hpos : (J.complexField e (fun j => Complex.I • e j) x).PosDef)
    (v : E) (hv : v ≠ 0) :
    0 < J.hessian x v v + J.hessian x (Complex.I • v) (Complex.I • v) := by
  let z : Fin 2 → ℂ := fun j => e.repr v j
  let Q : Matrix (Fin 2) (Fin 2) ℂ := fun _ j => z j
  have hz : z ≠ 0 := by
    intro he
    apply hv
    have hs := e.sum_repr v
    have hzj (j : Fin 2) : e.repr v j = 0 := congrFun he j
    simpa only [hzj,zero_smul,Finset.sum_const_zero] using hs.symm
  have hstar : star z ≠ 0 := by simpa only [star_ne_zero] using hz
  have hp := hpos.dotProduct_mulVec_pos hstar
  have hform : (Q * J.complexField e (fun j => Complex.I • e j) x * Q.conjTranspose) 0 0 =
      star (star z) ⬝ᵥ (J.complexField e (fun j => Complex.I • e j) x).mulVec (star z) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Q,star_star,star_apply,
      dotProduct,Matrix.mulVec,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    rfl
  have hvframe : complexFrameReal Q e (fun j => Complex.I • e j) 0 = v := by
    rw [complexFrameReal_complex_basis]
    exact e.sum_repr v
  have hIframe : complexFrameImag Q e (fun j => Complex.I • e j) 0 = Complex.I • v := by
    rw [complexFrameImag_eq_I_smul,hvframe]
  rw [← hform,← closure_complexField_complexFrame_two hU hu J e
    (fun j => Complex.I • e j) Q hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  change 0 < (jetComplexHessian (complexFrameReal Q e (fun j => Complex.I • e j))
    (complexFrameImag Q e (fun j => Complex.I • e j)) (J.hessian x) 0 0).re at hr
  simp only [jetComplexHessian,hvframe,hIframe] at hr
  norm_num [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.mul_im] at hr
  linarith

variable [FiniteDimensional ℝ E]

theorem classicalDirichlet_boundary_strict_jet_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundaryRegular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) :
    ∀ x ∈ frontier U, J.derivative x ≠ 0 ∧
      (∀ v : E, v ≠ 0 →
        0 < J.hessian x v v + J.hessian x (Complex.I • v) (Complex.I • v)) := by
  intro x hx
  refine ⟨classicalDirichlet_boundary_derivative_ne_zero_two hU hconv hK hboundaryRegular
    hu J hb e (fun j => Complex.I • e j) hab hpsh hdet x hx,?_⟩
  exact closure_complexField_posDef_paired_hessian_two hU hu J e (frontier_subset_closure hx)
    (closure_complexField_posDef_of_constantDensity J hU hu e (fun j => Complex.I • e j)
      one_ne_zero hdet hpsh x (frontier_subset_closure hx))

end PowerConvexity
