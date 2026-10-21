import FCAppendix.Affine.Uniform06.ExponentialMoments
import FCAppendix.Affine.Uniform07.Parameters

noncomputable section
namespace FCAppendix.Affine.Uniform06.KernelLeadingTerms

def leadingC (scale b m nu theta : ℝ) : ℝ :=
  scale / (b * m * nu * theta ^ 2)

def leadingCPrime (scale xi b theta : ℝ) : ℝ :=
  scale / (xi * b * theta)

def leadingR (scale b m nu theta : ℝ) : ℝ :=
  2 * scale / (b ^ 2 * m ^ 2 * nu ^ 2 * theta ^ 3)

def leadingRPrime (scale xi b m nu theta : ℝ) : ℝ :=
  2 * scale / (xi * b ^ 2 * m * nu * theta ^ 2)

theorem leadingC_pos {scale b m nu theta : ℝ}
    (hs : 0 < scale) (hb : 0 < b) (hm : 0 < m)
    (hnu : 0 < nu) (htheta : 0 < theta) :
    0 < leadingC scale b m nu theta := by
  unfold leadingC
  positivity

theorem leading_derivative_ratio {scale xi b m nu theta : ℝ}
    (hs : scale ≠ 0) (hxi : xi ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hnu : nu ≠ 0) (htheta : theta ≠ 0) :
    leadingCPrime scale xi b theta / leadingC scale b m nu theta =
      m * theta * nu / xi := by
  unfold leadingCPrime leadingC
  field_simp [hs, hxi, hb, hm, hnu, htheta]

theorem leading_duplicate_ratio {scale xi b m nu theta : ℝ}
    (hs : scale ≠ 0) (hxi : xi ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hnu : nu ≠ 0) (htheta : theta ≠ 0) :
    leadingR scale b m nu theta / leadingC scale b m nu theta =
      2 / (xi * b * (m * theta * nu / xi)) := by
  unfold leadingR leadingC
  field_simp [hs, hxi, hb, hm, hnu, htheta]

theorem leading_duplicate_derivative_ratio {scale xi b m nu theta : ℝ}
    (hs : scale ≠ 0) (hxi : xi ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hnu : nu ≠ 0) (htheta : theta ≠ 0) :
    leadingRPrime scale xi b m nu theta / leadingC scale b m nu theta =
      2 / (xi * b) := by
  unfold leadingRPrime leadingC
  field_simp [hs, hxi, hb, hm, hnu, htheta]

theorem leading_optimizer_advantage {scale eta xi b m nu theta v : ℝ}
    (hs : scale ≠ 0) (hxi : xi ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hnu : nu ≠ 0) (htheta : theta ≠ 0)
    (hfoc : (v - b) * leadingCPrime scale xi b theta =
      leadingC scale b m nu theta) :
    ((v - b) * (2 * leadingC scale b m nu theta - leadingR scale b m nu theta) -
        eta * b * leadingR scale b m nu theta) -
      (v - b) * leadingC scale b m nu theta =
      ((v - b) * leadingC scale b m nu theta) *
        (1 - 2 * eta / xi - 2 / (b * m * nu * theta)) := by
  have hd : leadingCPrime scale xi b theta ≠ 0 := by
    unfold leadingCPrime
    exact div_ne_zero hs (mul_ne_zero (mul_ne_zero hxi hb) htheta)
  have hshort : v - b = xi / (m * nu * theta) := by
    calc
      v - b = leadingC scale b m nu theta / leadingCPrime scale xi b theta :=
        (eq_div_iff hd).mpr hfoc
      _ = _ := by
        unfold leadingC leadingCPrime
        field_simp [hs, hxi, hb, hm, hnu, htheta]
  rw [hshort]
  unfold leadingC leadingR
  field_simp [hs, hxi, hb, hm, hnu, htheta]
  ring

theorem source_route_coefficient_positive (i : Uniform07.Row) :
    0 < 1 - 2 * Uniform07.eta i / Uniform07.xi i :=
  Uniform07.route_coefficient_pos i

end FCAppendix.Affine.Uniform06.KernelLeadingTerms
