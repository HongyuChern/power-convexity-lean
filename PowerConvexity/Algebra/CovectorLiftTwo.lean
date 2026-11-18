import PowerConvexity.Algebra.MinkowskiDeterminantTwo

/-! # A positive linear lift of two-dimensional Hermitian matrices

For p fixed and q=(-conj p_1,conj p_0), the linear map
L_p(X)=X+(p*Xp) q q* satisfies det L_p(X)=det X+(p*Xp)^2.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexOrder
open Matrix
namespace PowerConvexity

noncomputable def covectorValueTwo (p : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  star p ⬝ᵥ X.mulVec p

noncomputable def cofactorCovectorTwo (p : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-star (p 1),star (p 0)]

noncomputable def covectorLiftTwo (p : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  X+covectorValueTwo p X • vecMulVec (cofactorCovectorTwo p) (star (cofactorCovectorTwo p))

theorem covectorValueTwo_add (p : Fin 2 → ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    covectorValueTwo p (X+Y) = covectorValueTwo p X+covectorValueTwo p Y := by
  simp only [covectorValueTwo,add_mulVec,dotProduct_add]

theorem covectorValueTwo_smul (p : Fin 2 → ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    covectorValueTwo p (c • X) = c*covectorValueTwo p X := by
  simp only [covectorValueTwo,smul_mulVec,dotProduct_smul,smul_eq_mul]

theorem covectorValueTwo_nonneg (p : Fin 2 → ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X.PosSemidef) : 0 ≤ covectorValueTwo p X := hX.dotProduct_mulVec_nonneg p

theorem covectorLiftTwo_add (p : Fin 2 → ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    covectorLiftTwo p (X+Y) = covectorLiftTwo p X+covectorLiftTwo p Y := by
  simp only [covectorLiftTwo,covectorValueTwo_add,add_smul]
  abel

theorem covectorLiftTwo_smul (p : Fin 2 → ℂ) (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    covectorLiftTwo p (c • X) = c • covectorLiftTwo p X := by
  simp only [covectorLiftTwo,covectorValueTwo_smul,smul_add,smul_smul]

theorem covectorLiftTwo_posSemidef (p : Fin 2 → ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X.PosSemidef) : (covectorLiftTwo p X).PosSemidef :=
  hX.add ((posSemidef_vecMulVec_self_star _).smul (covectorValueTwo_nonneg p hX))

theorem covectorLiftTwo_posDef (p : Fin 2 → ℂ) {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X.PosDef) : (covectorLiftTwo p X).PosDef :=
  hX.add_posSemidef ((posSemidef_vecMulVec_self_star _).smul (covectorValueTwo_nonneg p hX.posSemidef))

theorem covectorLiftTwo_det (p : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (covectorLiftTwo p X).det = X.det+(covectorValueTwo p X)^2 := by
  simp only [covectorLiftTwo,covectorValueTwo,cofactorCovectorTwo,det_fin_two,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,mulVec,dotProduct,
    Fin.sum_univ_two,Pi.star_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,star_neg,star_star]
  ring

end PowerConvexity
