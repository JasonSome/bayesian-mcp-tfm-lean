import FCAppendix.Affine.Hybrid.CountRegionData

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical

theorem typical_count_point_errors {M c A H₀ H₁ : ℕ} {ρ a h z δ : ℝ}
    (hM : 0 < M) (hδ : 0  ≤  δ) (hz0 : 0  ≤  z) (hz1 : z  ≤  1)
    (hcap : |(c:ℝ)-(M:ℝ)*ρ|  ≤  M*δ) (hactive : |(A:ℝ)-(M:ℝ)*a|  ≤  M*δ)
    (hupper₀ : |(H₀:ℝ)-(M:ℝ)*(h/2)|  ≤  M*δ)
    (hupper₁ : |(H₁:ℝ)-(M:ℝ)*(h/2)|  ≤  M*δ)
    (hlower : 2*δ<ρ-h/2) (hupper : 3*δ<a+h/2-ρ) :
    let d₀:=activeResidual c A H₀
    let d₁:=activeResidual c A H₁
    let p:=finiteCountPoint M A (min d₀ d₁) (exclusiveQuota z A) (residualDifference d₀ d₁)
    |p 0-sourceCountPoint a h ρ z 0|  ≤  δ ∧
    |p 1-sourceCountPoint a h ρ z 1|  ≤  2*δ ∧
    |p 2-sourceCountPoint a h ρ z 2|  ≤  δ+1/(M:ℝ) ∧
    |p 3-sourceCountPoint a h ρ z 3|  ≤  4*δ := by
  have hm : (0:ℝ)<M:=Nat.cast_pos.mpr hM
  have hc:=abs_le.mp hcap
  have ha:=abs_le.mp hactive
  have hh₀:=abs_le.mp hupper₀
  have hh₁:=abs_le.mp hupper₁
  have hi:=active_residuals_interior_of_close hM hcap hactive hupper₀ hupper₁ hlower hupper
  let d₀:=activeResidual c A H₀
  let d₁:=activeResidual c A H₁
  have hd₀ : (d₀:ℝ)=(c:ℝ)-H₀:=by
    change (activeResidual c A H₀:ℝ)=_
    rw [hi.2.2.2.2.1,Nat.cast_sub hi.1.le]
  have hd₁ : (d₁:ℝ)=(c:ℝ)-H₁:=by
    change (activeResidual c A H₁:ℝ)=_
    rw [hi.2.2.2.2.2.1,Nat.cast_sub hi.2.1.le]
  have hb₀ : |(d₀:ℝ)-(M:ℝ)*(ρ-h/2)|  ≤  2*(M:ℝ)*δ:=by rw [hd₀,abs_le];constructor <;> nlinarith
  have hb₁ : |(d₁:ℝ)-(M:ℝ)*(ρ-h/2)|  ≤  2*(M:ℝ)*δ:=by rw [hd₁,abs_le];constructor <;> nlinarith
  have hsmall : |((min d₀ d₁:ℕ):ℝ)-(M:ℝ)*(ρ-h/2)|  ≤  2*(M:ℝ)*δ:=by
    rcases le_total d₀ d₁ with he|he
    · simpa only [min_eq_left he] using hb₀
    · simpa only [min_eq_right he] using hb₁
  have hgap : (residualDifference d₀ d₁:ℝ)  ≤  4*(M:ℝ)*δ:=by
    have hb₀':=abs_le.mp hb₀
    have hb₁':=abs_le.mp hb₁
    unfold residualDifference
    rw [Nat.cast_sub (show min d₀ d₁ ≤ max d₀ d₁ from min_le_max)]
    rcases le_total d₀ d₁ with he|he
    · rw [max_eq_right he,min_eq_left he]
      nlinarith
    · rw [max_eq_left he,min_eq_right he]
      nlinarith
  have hfloor₀ : (exclusiveQuota z A:ℝ)  ≤  z*(A:ℝ)/2:=Nat.floor_le (by positivity)
  have hfloor₁ : z*(A:ℝ)/2<(exclusiveQuota z A:ℝ)+1:=Nat.lt_floor_add_one _
  have hround : |(exclusiveQuota z A:ℝ)-(M:ℝ)*(z*a/2)|  ≤  (M:ℝ)*δ+1 := by
    have hmul₀:=mul_le_mul_of_nonneg_left ha.1 hz0
    have hmul₁:=mul_le_mul_of_nonneg_left ha.2 hz0
    have htol : z*((M:ℝ)*δ)  ≤  (M:ℝ)*δ:=mul_le_of_le_one_left (mul_nonneg hm.le hδ) hz1
    rw [abs_le]
    constructor <;> nlinarith
  have hdivide (x t B : ℝ) (he : |x-(M:ℝ)*t|  ≤  (M:ℝ)*B) : |x/(M:ℝ)-t|  ≤  B:=by
    have hx : x/(M:ℝ)-t=(x-(M:ℝ)*t)/(M:ℝ):=by field_simp
    rw [hx,abs_div,abs_of_pos hm]
    exact (div_le_iff₀ hm).mpr (by nlinarith)
  change |(A:ℝ)/(M:ℝ)-a| ≤ δ ∧
    |((min d₀ d₁:ℕ):ℝ)/(M:ℝ)-(ρ-h/2)| ≤ 2*δ ∧
    |(exclusiveQuota z A:ℝ)/(M:ℝ)-z*a/2| ≤ δ+1/(M:ℝ) ∧
    |(residualDifference d₀ d₁:ℝ)/(M:ℝ)-0| ≤ 4*δ
  refine ⟨hdivide _ _ _ hactive,hdivide _ _ _ (by nlinarith [hsmall]),?_,?_⟩
  · apply hdivide
    have he : (M:ℝ)*(δ+1/(M:ℝ))=(M:ℝ)*δ+1:=by field_simp
    rw [he]
    exact hround
  · rw [sub_zero,abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hm).mpr (by nlinarith)

end FCAppendix.Affine.Hybrid
