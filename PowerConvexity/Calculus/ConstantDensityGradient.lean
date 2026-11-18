import PowerConvexity.Calculus.ConstantDensity

/-! # The vanishing third-derivative contractions used after `2_2_12`

These vanish by the first differentiated determinant equation and genuine
commutation of derivatives.  No third-order tensor is independently assigned.
-/

set_option autoImplicit false
open scoped ContDiff Topology BigOperators

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem third_inner_comm_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (a b c d e k : E) :
    dz a b (dz c d (dz e k f)) x = dz a b (dz e k (dz c d f)) x := by
  apply dz_congr_nhds (a := a) (b := b)
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (m := 2) (by norm_num)).eventually (by simp)
  exact hn.mono fun y hy => dz_comm_at hy c d e k

theorem third_reverse_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (a b c d e k : E) :
    dz a b (dz c d (dz e k f)) x = dz e k (dz c d (dz a b f)) x := by
  rw [third_outer_comm_at hf, third_inner_comm_at hf, third_outer_comm_at hf]

theorem contracted_dzbar_pure_zero {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (i : ι) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (fun y => pureHessian a b u y i p) x) = 0 := by
  have hc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have he (p q : ι) :
      dz (a q) (-b q) (fun y => pureHessian a b u y i p) x =
        dz (a i) (b i) (fun y => complexHessian a b u y p q) x := by
    change dz (a q) (-b q) (dz (a i) (b i) (dz (a p) (b p) _)) x = _
    rw [third_outer_comm_at hc, third_inner_comm_at hc]
    rfl
  simp only [he]
  exact complexHessian_det_const_first hu a b hdet (a i) (b i)

theorem contracted_dzbar_mixed_zero {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (j : ι) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (fun y => complexHessian a b u y p j) x) = 0 := by
  have hc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have he (p q : ι) :
      dz (a q) (-b q) (fun y => complexHessian a b u y p j) x =
        dz (a j) (-b j) (fun y => complexHessian a b u y p q) x :=
    third_reverse_at hc (a q) (-b q) (a p) (b p) (a j) (-b j)
  simp only [he]
  exact complexHessian_det_const_first hu a b hdet (a j) (-b j)

theorem contracted_dz_mixed_zero {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (i : ι) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a p) (b p) (fun y => complexHessian a b u y i q) x) = 0 := by
  have he (p q : ι) :
      dz (a p) (b p) (fun y => complexHessian a b u y i q) x =
        dz (a i) (b i) (fun y => complexHessian a b u y p q) x :=
    complexHessian_row_comm hu a b p i q
  simp only [he]
  exact complexHessian_det_const_first hu a b hdet (a i) (b i)

end PowerConvexity
