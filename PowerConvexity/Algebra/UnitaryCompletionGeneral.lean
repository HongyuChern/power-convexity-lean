import PowerConvexity.Algebra.TakagiRealification
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # General finite-dimensional normalization and unitary completion -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_unit_antilinear_vector {B : Matrix ι ι ℂ}
    (hB : B.transpose = B) (hB0 : B ≠ 0) :
    ∃ (u : ι → ℂ) (t : ℝ), t ≠ 0 ∧
      (∑ i, u i*star (u i)) = 1 ∧ B.mulVec u = (t:ℂ) • star u := by
  obtain ⟨z,t,ht,hz,he⟩ := exists_antilinear_eigenvector_of_symmetric hB hB0
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
  let S : ℝ := ∑ i, Complex.normSq (z i)
  have hS : 0 < S := Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (z i))
    ⟨j,Finset.mem_univ _,Complex.normSq_pos.mpr hj⟩
  let r := Real.sqrt S
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hrs : r*r = S := by simpa only [← pow_two] using Real.sq_sqrt hS.le
  let u : ι → ℂ := (r:ℂ)⁻¹ • star z
  have hu : ∑ i, Complex.normSq (u i) = 1 := by
    simp only [u,Pi.smul_apply,Pi.star_apply,smul_eq_mul,map_mul,Complex.normSq_inv,
      Complex.normSq_ofReal,Complex.star_def,Complex.normSq_conj]
    rw [← Finset.mul_sum,hrs]
    exact inv_mul_cancel₀ hS.ne'
  refine ⟨u,t,ht,?_,?_⟩
  · have h := congrArg Complex.ofReal hu
    simpa only [Complex.ofReal_sum,Complex.ofReal_one,Complex.star_def,Complex.mul_conj] using h
  · rw [Matrix.mulVec_smul,he]
    funext i
    change (r:ℂ)⁻¹*((t:ℂ)*z i) = (t:ℂ)*star ((r:ℂ)⁻¹*star (z i))
    simp only [star_mul,star_inv₀,Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
    ring

theorem exists_unitary_with_row (u : ι → ℂ) (hu : (∑ i, u i*star (u i)) = 1) (i : ι) :
    ∃ P : Matrix ι ι ℂ, P*P.conjTranspose = 1 ∧ ∀ j, P i j = u j := by
  classical
  let w : EuclideanSpace ℂ ι := WithLp.toLp 2 (star u)
  have hw : inner ℂ w w = 1 := by
    simpa only [w,PiLp.inner_apply,RCLike.inner_apply',WithLp.ofLp_toLp,Pi.star_apply,
      Complex.star_def, Complex.conj_conj, mul_comm] using hu
  have hv : Orthonormal ℂ (({i} : Set ι).domRestrict (fun _ : ι => w)) := by
    rw [orthonormal_iff_ite]
    intro j k
    have hj : j.val = i := Set.mem_singleton_iff.mp j.property
    have hk : k.val = i := Set.mem_singleton_iff.mp k.property
    have he : j = k := Subtype.ext (hj.trans hk.symm)
    simp only [he,ite_true,Set.domRestrict_apply]
    exact hw
  obtain ⟨v,hv⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι)
  let P : Matrix ι ι ℂ := fun j k => star (v j k)
  refine ⟨P,?_,?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp v.orthonormal j k
    simpa [P,Matrix.mul_apply,Matrix.conjTranspose_apply,
      PiLp.inner_apply,RCLike.inner_apply',RCLike.star_def, mul_comm, Matrix.one_apply] using h
  · intro j
    have hvi := hv i (by simp)
    change star (v i j) = u j
    rw [hvi]
    change star (star (u j)) = u j
    exact star_star _

theorem unitary_antilinear_first_column {B P : Matrix ι ι ℂ} (i : ι) (u : ι → ℂ) (t : ℝ)
    (hP : P*P.conjTranspose = 1) (hrow : ∀ j, P i j = u j)
    (he : B.mulVec u = (t:ℂ) • star u) (j : ι) :
    (P*B*P.transpose) j i = (t:ℂ)*(if j=i then 1 else 0) := by
  have hBP (k : ι) : (B*P.transpose) k i = (t:ℂ)*star (u k) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,hrow]
    exact congrFun he k
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  simp only [hBP]
  calc
    _ = (t:ℂ)*(P*P.conjTranspose) j i := by
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,hrow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hP]; rfl

end PowerConvexity
