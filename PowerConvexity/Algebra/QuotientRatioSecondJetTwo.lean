import PowerConvexity.Algebra.TraceDetRatioTwo

/-! # Exact second jet for the variable metric Schur quotient

At A=I and M=diag(a,b), (x,y,z,w) are the real Hermitian entries
of DA, (p,q,r,s) those of DM, and X,Y,U,V are diagonal second jets.
This is algebra for the actual chain rule, not a PDE estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PowerConvexity

theorem quotient_ratio_normalized_second_jet_two
    (a b p q r s x y z w U V X Y : ℝ) (ht : a+b ≠ 0) :
    let t := a+b
    let T1 := p+q+a*y+b*x
    let D1 := x+y
    let N1 := b*p+a*q
    let T2 := U+V+a*Y+b*X+2*(p*y+q*x)-4*(r*z+s*w)
    let D2 := X+Y+2*x*y-2*(z^2+w^2)
    let N2 := b*U+a*V+2*(p*q-r^2-s^2)
    T2-2*T1*D1-t*D2+2*t*D1^2+N2/t-
        (2*N1*T1+a*b*T2)/t^2+2*a*b*T1^2/t^3 =
      (1+b^2/t^2)*(U-2*p*x-2*(r*z+s*w)+2*a*(x^2+z^2+w^2)-a*X)+
      (1+a^2/t^2)*(V-2*q*y-2*(r*z+s*w)+2*b*(y^2+z^2+w^2)-b*Y)-
      2*((b*(p-a*x)-a*(q-b*y))^2+
        t^2*((r-a*z)*(r-b*z)+(s-a*w)*(s-b*w)))/t^3 := by
  dsimp only
  field_simp [ht]
  <;> ring

theorem quotient_ratio_normalized_first_jet_two
    (a b p q x y : ℝ) (ht : a+b ≠ 0) :
    let t := a+b
    (p+q+a*y+b*x)-t*(x+y)+(b*p+a*q)/t-a*b*(p+q+a*y+b*x)/t^2 =
      (1+b^2/t^2)*(p-a*x)+(1+a^2/t^2)*(q-b*y) := by
  dsimp only
  field_simp [ht]
  <;> ring

end PowerConvexity
