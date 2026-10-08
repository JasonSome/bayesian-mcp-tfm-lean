import FCAppendix.PayOnce.LimitFormulas
import FCAppendix.PayOnce.ResponseFactor
import FCAppendix.PayOnce.KernelTailEvent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace FCAppendix.PayOnce.FiniteFOCResponse
open Set Real CommonList OwnImpact RareSuccessSlope ResponseFactor

theorem foc_positivity {b w Q R : ℝ} (hb : 0 < b) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFOC : b*Q = (w-b)*R) : 0 < R ∧ b < w := by
  have hprod := mul_pos hb hQ
  have hRp : 0 < R := by
    by_contra hh
    have hz : R = 0 := le_antisymm (le_of_not_gt hh) hR
    rw [hz,mul_zero] at hFOC
    linarith
  refine ⟨hRp,?_⟩
  by_contra hh
  have hwb : w-b ≤ 0 := by linarith
  have hnon := mul_nonpos_of_nonpos_of_nonneg hwb hR
  linarith

theorem foc_rpow_identity {L b w Q R γ : ℝ} (hL : 0 ≤ L) (hb : 0 < b)
    (hQ : 0 < Q) (hR : 0 ≤ R) (hFOC : b*Q = (w-b)*R) :
    (L/w)^γ = (L/(b*(Q+R)))^γ*R^γ := by
  have hp := foc_positivity hb hQ hR hFOC
  have hw : 0 < w := hb.trans hp.2
  have hsum : 0 < Q+R := add_pos_of_pos_of_nonneg hQ hR
  have he : w*R = b*(Q+R) := by nlinarith
  have hratio : L/w = (L/(b*(Q+R)))*R := by
    rw [← he]
    field_simp [hp.1.ne']
  rw [hratio,Real.mul_rpow (div_nonneg hL (mul_pos hb hsum).le) hR]

theorem product_error_le {A x B y K Z ex eA : ℝ}
    (hA : |A| ≤ K) (hy : |y| ≤ Z) (hx : |x-y| ≤ ex) (hB : |A-B| ≤ eA) :
    |A*x-B*y| ≤ K*ex+Z*eA := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hA
  have heA : 0 ≤ eA := (abs_nonneg _).trans hB
  calc
    |A*x-B*y| = |A*(x-y)+(A-B)*y| := by congr 1; ring
    _ ≤ |A*(x-y)|+|(A-B)*y| := abs_add_le _ _
    _ = |A| *|x-y|+|A-B| *|y| := by rw [abs_mul,abs_mul]
    _ ≤ K*ex+eA*Z := add_le_add (mul_le_mul hA hx (abs_nonneg _) hK)
      (mul_le_mul hB hy (abs_nonneg _) heA)
    _ = K*ex+Z*eA := by ring

theorem inverse_rpow_difference_le {γ d x y : ℝ} (hγ : 0 ≤ γ) (hd : 0 < d)
    (hx : d ≤ x) (hy : d ≤ y) :
    |x^(-γ)-y^(-γ)| ≤ (γ*d^(-γ-1))*|x-y| := by
  have hderiv (z : ℝ) (hz : z ∈ Ici d) :
      HasDerivAt (fun v : ℝ => v^(-γ)) ((-γ)*z^(-γ-1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (hd.trans_le hz).ne')
  have hbound (z : ℝ) (hz : z ∈ Ici d) :
      ‖deriv (fun v : ℝ => v^(-γ)) z‖ ≤ γ*d^(-γ-1) := by
    rw [(hderiv z hz).deriv,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hγ,
      abs_of_nonneg (Real.rpow_nonneg (hd.trans_le hz).le _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hd hz (by linarith : -γ-1 ≤ 0)) hγ
  have hh := (convex_Ici d).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hderiv z hz).differentiableAt) hbound hy hx
  simpa only [Real.norm_eq_abs] using hh

theorem power_difference_le {k : ℕ} {x y B e : ℝ}
    (hx : x ∈ Icc (0:ℝ) B) (hy : y ∈ Icc (0:ℝ) B) (he : |x-y| ≤ e) :
    |x^k-y^k| ≤ ((k:ℝ)*B^(k-1))*e := by
  have hmax : max |x| |y| ≤ B := by
    rw [abs_of_nonneg hx.1,abs_of_nonneg hy.1]
    exact max_le hx.2 hy.2
  have hp := abs_pow_sub_pow_le x y k
  have hB : 0 ≤ B := hx.1.trans hx.2
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hpow : max |x| |y|^(k-1) ≤ B^(k-1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _
  calc
    |x^k-y^k| ≤ |x-y| *(k:ℝ)*max |x| |y|^(k-1) := hp
    _ ≤ e*(k:ℝ)*B^(k-1) := mul_le_mul
      (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg k)) hpow
      (pow_nonneg (le_max_of_le_left (abs_nonneg _)) _) (by positivity)
    _ = ((k:ℝ)*B^(k-1))*e := by ring

theorem response_error_of_coefficient_error {n : ℕ} (hn : 2 ≤ n)
    {L b w Q R p A₀ z₀ K Z eR eA : ℝ}
    (hL : 0 < L) (hLb : L < b) (hQ : 0 < Q) (hR : 0 ≤ R)
    (hFOC : b*Q = (w-b)*R)
    (hdet : A₀*z₀ = 1-p)
    (hA : |(L/(b*(Q+R)))^(1/((n:ℝ)-1))| ≤ K) (hz : |z₀| ≤ Z)
    (hroot : |R^(1/((n:ℝ)-1))-z₀| ≤ eR)
    (hcoeff : |(L/(b*(Q+R)))^(1/((n:ℝ)-1))-A₀| ≤ eA) :
    |p-Limit.pStar n L w| ≤ K*eR+Z*eA := by
  have hp := foc_positivity (hL.trans hLb) hQ hR hFOC
  have hstar := Limit.pStar_of_lt hn hL.le (hLb.trans hp.2)
  have hid := foc_rpow_identity (γ := 1/((n:ℝ)-1)) hL.le (hL.trans hLb) hQ hR hFOC
  have hh := product_error_le hA hz hroot hcoeff
  rw [← hid,hdet] at hh
  rw [hstar]
  convert hh using 1
  congr 1
  ring

theorem coefficient_eq {L b X γ : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hX : 0 < X) :
    (L/(b*X))^γ = (L/b)^γ*X^(-γ) := by
  have he : L/(b*X) = (L/b)/X := by ring
  rw [he,Real.div_rpow (div_nonneg hL hb.le) hX.le,Real.rpow_neg hX.le]
  rfl

theorem coefficient_abs_le {L b X γ d : ℝ} (hL : 0 ≤ L) (hb : 0 < b)
    (hLb : L ≤ b) (hγ : 0 ≤ γ) (hd : 0 < d) (hX : d ≤ X) :
    |(L/(b*X))^γ| ≤ d^(-γ) := by
  have hXp := hd.trans_le hX
  rw [coefficient_eq hL hb hXp,abs_mul,
    abs_of_nonneg (rpow_nonneg (div_nonneg hL hb.le) _),
    abs_of_nonneg (rpow_nonneg hXp.le _)]
  have hr : (L/b)^γ ≤ 1 := rpow_le_one (div_nonneg hL hb.le) ((div_le_one hb).mpr hLb) hγ
  have hi := rpow_le_rpow_of_nonpos hd hX (neg_nonpos.mpr hγ)
  exact (mul_le_of_le_one_left (rpow_nonneg hXp.le _) hr).trans hi

theorem coefficient_difference_le {L b X Y γ d : ℝ} (hL : 0 ≤ L) (hb : 0 < b)
    (hLb : L ≤ b) (hγ : 0 ≤ γ) (hd : 0 < d) (hX : d ≤ X) (hY : d ≤ Y) :
    |(L/(b*X))^γ-(L/(b*Y))^γ| ≤ (γ*d^(-γ-1))*|X-Y| := by
  rw [coefficient_eq hL hb (hd.trans_le hX),coefficient_eq hL hb (hd.trans_le hY),
    ← mul_sub,abs_mul,abs_of_nonneg (rpow_nonneg (div_nonneg hL hb.le) _)]
  have hr : (L/b)^γ ≤ 1 := rpow_le_one (div_nonneg hL hb.le) ((div_le_one hb).mpr hLb) hγ
  exact (mul_le_of_le_one_left (abs_nonneg _) hr).trans (inverse_rpow_difference_le hγ hd hX hY)

theorem deterministic_coefficient_identity {n : ℕ} (hn : 2 ≤ n) {L b : ℝ}
    (hL : 0 < L) (hLb : L < b) :
    (L/(b*(success n (kernel n b L)+phi n (kernel n b L))))^(1/((n:ℝ)-1))*
      rootFactor n (kernel n b L) = 1-kernel n b L := by
  let p := kernel n b L
  have hp : p ∈ Icc (0:ℝ) 1 := KernelTailEvent.kernel_bounds hn hL b
  have hb : 0 < b := hL.trans hLb
  change (L/(b*(success n p+phi n p)))^(1/((n:ℝ)-1))*rootFactor n p = 1-p
  by_cases hp1 : p = 1
  · rw [hp1,rootFactor,sub_self,mul_zero,mul_zero]
  · have hp0 : 0 < p := by
      apply lt_of_le_of_ne hp.1
      intro he
      have hz : kernel n b L = 0 := he.symm
      exact hLb.not_ge ((kernel_eq_zero_iff n hn hb hL).mp hz)
    have hpi : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hscore : b*H n p = L := (scalarThreshold_kernel n hn hb hL).2.2.2.2 hp0 hpi
    have hJ := J_pos hn hp
    have hden : b*(success n p+phi n p) = L*J n p := by
      rw [success_add_phi_eq_J_mul_H hn hp]
      nlinarith [hscore]
    have hr : (L/(b*(success n p+phi n p)))*J n p = 1 := by
      rw [hden]
      field_simp
    have hdenp : 0 < b*(success n p+phi n p) := by rw [hden]; positivity
    rw [rootFactor,← mul_assoc,← Real.mul_rpow (div_nonneg hL.le hdenp.le) hJ.le,
      hr,Real.one_rpow,one_mul]

theorem response_factor_error_le {n : ℕ} (hn : 2 ≤ n) {p R e : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (he1 : e ≤ 1)
    (herr : |R^(1/((n:ℝ)-1))-rootFactor n p| ≤ e) :
    |R-phi n p| ≤
      (((n-1:ℕ):ℝ)*(((n:ℝ)^2)^(1/((n:ℝ)-1))+1)^((n-1)-1))*e := by
  let Z := ((n:ℝ)^2)^(1/((n:ℝ)-1))
  let x := R^(1/((n:ℝ)-1))
  have hroot := rootFactor_bounds hn hp
  change 0 ≤ rootFactor n p ∧ rootFactor n p ≤ Z at hroot
  have hx : x ∈ Icc (0:ℝ) (Z+1) := by
    refine ⟨rpow_nonneg hR _,?_⟩
    have hh := (abs_le.mp herr).2
    change x-rootFactor n p ≤ e at hh
    linarith [hroot.2]
  have hy : rootFactor n p ∈ Icc (0:ℝ) (Z+1) := ⟨hroot.1,hroot.2.trans (by linarith)⟩
  have hpow : x^(n-1) = R := by
    dsimp only [x]
    have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by
      rw [Nat.cast_sub (by omega),Nat.cast_one,one_div]
    rw [hexp,rpow_inv_natCast_pow hR (by omega)]
  have hh := power_difference_le (k := n-1) hx hy herr
  rw [hpow,rootFactor_pow hn hp] at hh
  exact hh

theorem exists_uniform_response_error_constant {n : ℕ} (hn : 2 ≤ n)
    {q₀ : ℝ} (hq₀ : 0 < q₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ L b w Q R e : ℝ,
      0 < L → L < b → q₀ ≤ Q → 0 ≤ R → b*Q = (w-b)*R →
      e ≤ min 1 (q₀/2) →
      |Q-success n (kernel n b L)| ≤ e →
      |R^(1/((n:ℝ)-1))-rootFactor n (kernel n b L)| ≤ e →
      |kernel n b L-Limit.pStar n L w| ≤ C*e := by
  let γ := 1/((n:ℝ)-1)
  let Z := ((n:ℝ)^2)^γ
  let P := ((n-1:ℕ):ℝ)*(Z+1)^((n-1)-1)
  let d := q₀/2
  let K := d^(-γ)
  let D := γ*d^(-γ-1)
  have hγ : 0 < γ := Limit.exponent_pos hn
  have hZ : 0 ≤ Z := rpow_nonneg (sq_nonneg _) _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hd : 0 < d := half_pos hq₀
  have hK : 0 < K := rpow_pos_of_pos hd _
  have hD : 0 < D := mul_pos hγ (rpow_pos_of_pos hd _)
  refine ⟨K+Z*D*(1+P),by positivity,?_⟩
  intro L b w Q R e hL hLb hQ hR hFOC he hQerr hRroot
  let p := kernel n b L
  have hp : p ∈ Icc (0:ℝ) 1 := KernelTailEvent.kernel_bounds hn hL b
  have hb : 0 < b := hL.trans hLb
  have hQpos : 0 < Q := hq₀.trans_le hQ
  have hroot := rootFactor_bounds hn hp
  have hRerr : |R-phi n p| ≤ P*e :=
    response_factor_error_le hn hp hR (he.trans (min_le_left _ _)) hRroot
  have hSfloor : d ≤ success n p := by
    have hdiff := (abs_le.mp hQerr).2
    have he2 := he.trans (min_le_right _ _)
    dsimp only [d]
    change Q-success n p ≤ e at hdiff
    linarith
  have hX : d ≤ Q+R := by dsimp only [d]; linarith
  have hY : d ≤ success n p+phi n p := by linarith [phi_nonneg hn hp]
  have hXY : |(Q+R)-(success n p+phi n p)| ≤ (1+P)*e := by
    calc
      |(Q+R)-(success n p+phi n p)| = |(Q-success n p)+(R-phi n p)| := by congr 1; ring
      _ ≤ |Q-success n p|+|R-phi n p| := abs_add_le _ _
      _ ≤ e+P*e := add_le_add hQerr hRerr
      _ = (1+P)*e := by ring
  have hcoeff : |(L/(b*(Q+R)))^γ-(L/(b*(success n p+phi n p)))^γ| ≤
      (D*(1+P))*e := by
    have hh := coefficient_difference_le hL.le hb hLb.le hγ.le hd hX hY
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hXY hD.le)
    simpa only [D,mul_assoc] using hh'
  have hA : |(L/(b*(Q+R)))^γ| ≤ K := coefficient_abs_le hL.le hb hLb.le hγ.le hd hX
  have hz : |rootFactor n p| ≤ Z := by
    rw [abs_of_nonneg hroot.1]
    exact hroot.2
  have hh := response_error_of_coefficient_error hn hL hLb hQpos hR hFOC
    (deterministic_coefficient_identity hn hL hLb) hA hz hRroot hcoeff
  change |p-Limit.pStar n L w| ≤ _ at hh ⊢
  calc
    |p-Limit.pStar n L w| ≤ K*e+Z*((D*(1+P))*e) := hh
    _ = (K+Z*D*(1+P))*e := by ring

theorem one_sub_pStar_le_derivative_root {n : ℕ} (hn : 2 ≤ n)
    {L b w Q R q₀ : ℝ} (hL : 0 < L) (hLb : L ≤ b) (hq₀ : 0 < q₀)
    (hQ : q₀ ≤ Q) (hR : 0 ≤ R) (hFOC : b*Q = (w-b)*R) :
    1-Limit.pStar n L w ≤ q₀^(-(1/((n:ℝ)-1)))*R^(1/((n:ℝ)-1)) := by
  have hb : 0 < b := hL.trans_le hLb
  have hQpos := hq₀.trans_le hQ
  have hp := foc_positivity hb hQpos hR hFOC
  rw [Limit.pStar_of_lt hn hL.le (hLb.trans_lt hp.2),sub_sub_cancel]
  rw [foc_rpow_identity hL.le hb hQpos hR hFOC]
  apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hR _)
  exact (le_abs_self _).trans (coefficient_abs_le hL.le hb hLb (Limit.exponent_pos hn).le
    hq₀ (by linarith))

end FCAppendix.PayOnce.FiniteFOCResponse
