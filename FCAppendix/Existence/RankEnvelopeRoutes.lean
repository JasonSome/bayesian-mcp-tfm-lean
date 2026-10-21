import FCAppendix.Existence.RankEnvelopeIntegral
import FCAppendix.Finite.NestedRouting

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set

def twoContactCount (z : Bool × Bool) : Fin 3 :=
  ⟨(if z.1 then 1 else 0)+(if z.2 then 1 else 0),by rcases z with ⟨a,b⟩; cases a <;> cases b <;> decide⟩

def twoContactLaw (mu : FiniteLaw (Bool × Bool)) : CountLaw 2 := mu.map twoContactCount

theorem twoContact_duplicates (mu : FiniteLaw (Bool × Bool)) :
    (twoContactLaw mu).duplicates=mu.prob (fun z => z.1=true ∧ z.2=true) := by
  rw [CountLaw.duplicates_eq_expect,twoContactLaw,FiniteLaw.expect_map,FiniteLaw.prob_eq_expect]
  apply FiniteLaw.expect_congr
  rintro ⟨a,b⟩
  cases a <;> cases b <;> norm_num [twoContactCount,successIndicator]

theorem twoContact_duplicates_lower (mu : FiniteLaw (Bool × Bool)) (delta : ℝ)
    (hleft : 1-delta ≤ mu.prob (fun z => z.1=true))
    (hright : 1-delta ≤ mu.prob (fun z => z.2=true)) :
    1-2*delta ≤ (twoContactLaw mu).duplicates := by
  rw [twoContact_duplicates]
  have hh := Finite.pair_acceptance_from_marginals mu (fun z => z.1=true) (fun z => z.2=true)
    (1-delta) hleft hright
  linarith

theorem affine_zero_base_utility (mu : CountLaw 2) (eta v b : ℝ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (G : Schedule 2) :
    mu.utility v b 0 (Schedule.affine 2 eta h0 h1) G =
      (v-b)*mu.success-eta*b*mu.duplicates := by
  rw [CountLaw.utility_eq,CountLaw.charge_affine]
  ring

theorem two_route_upper_bound (mu : CountLaw 2) {eta R delta v b : ℝ}
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hR : 0 ≤ R) (hRb : R ≤ b) (hbv : b ≤ v)
    (hdelta : 0 ≤ 1-2*delta) (hD : 1-2*delta ≤ mu.duplicates) (G : Schedule 2) :
    mu.utility v b 0 (Schedule.affine 2 eta h0 h1) G ≤ v-R-eta*R*(1-2*delta) := by
  rw [affine_zero_base_utility]
  have hS := mul_le_mul_of_nonneg_left mu.success_le_one (sub_nonneg.mpr hbv)
  have hcost := mul_le_mul_of_nonneg_left hD (mul_nonneg h0 (hR.trans hRb))
  have hfloor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hRb h0) hdelta
  nlinarith

theorem affine_above_value_nonpositive (mu : CountLaw 2) {eta v b : ℝ}
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hb : 0 ≤ b) (hvb : v ≤ b) (G : Schedule 2) :
    mu.utility v b 0 (Schedule.affine 2 eta h0 h1) G ≤ 0 := by
  rw [affine_zero_base_utility]
  have hS := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvb) mu.success_nonneg
  have hcost := mul_nonneg (mul_nonneg h0 hb) mu.duplicates_nonneg
  linarith

theorem hidden_two_route_excluded {q : ℝ → ℝ} (hq : Monotone q)
    (hq1 : ∀ x, q x ≤ 1) {t R eta delta v b : ℝ}
    (hR : 0 < R) (hRt : R<t) (hqt : 0 < q t)
    (hint : IntegrableOn (fun x => 1-q x) (Ioi t))
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hguard : error q t R<eta*R*(1-2*delta))
    (htv : t ≤ v) (hRb : R ≤ b) (mu : FiniteLaw (Bool × Bool))
    (hleft : 1-delta ≤ mu.prob (fun z => z.1=true))
    (hright : 1-delta ≤ mu.prob (fun z => z.2=true)) (G : Schedule 2) :
    (twoContactLaw mu).utility v b 0 (Schedule.affine 2 eta h0 h1) G < utility q t R v := by
  by_cases hbv : b ≤ v
  · have hE := error_nonneg hRt.le hq1
    have hprod : 0 < eta*R*(1-2*delta) := hE.trans_lt hguard
    have hdelta : 0 ≤ 1-2*delta := by
      by_contra hbad
      have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0 hR.le) (le_of_not_ge hbad)
      linarith
    have hu := two_route_upper_bound (twoContactLaw mu) h0 h1 hR.le hRb hbv hdelta
      (twoContact_duplicates_lower mu delta hleft hright) G
    have hU := utility_error_bound hq (R:=R) htv hq1 hint
    linarith
  · exact (affine_above_value_nonpositive (twoContactLaw mu) h0 h1 (hR.le.trans hRb)
      (le_of_not_ge hbv) G).trans_lt (utility_pos hq hRt hqt htv)

theorem hidden_two_route_below_floor {q : ℝ → ℝ} (hq1 : ∀ x, q x ≤ 1)
    {t R eta delta v b : ℝ} (hR : 0 < R) (hRt : R<t) (hRv : R ≤ v) (hvt : v ≤ t)
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hguard : error q t R<eta*R*(1-2*delta))
    (hRb : R ≤ b) (mu : FiniteLaw (Bool × Bool))
    (hleft : 1-delta ≤ mu.prob (fun z => z.1=true))
    (hright : 1-delta ≤ mu.prob (fun z => z.2=true)) (G : Schedule 2) :
    (twoContactLaw mu).utility v b 0 (Schedule.affine 2 eta h0 h1) G < (v-R)*q t := by
  have hE := error_nonneg hRt.le hq1
  have hprod : 0 < eta*R*(1-2*delta) := hE.trans_lt hguard
  have hdelta : 0 ≤ 1-2*delta := by
    by_contra hbad
    have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0 hR.le) (le_of_not_ge hbad)
    linarith
  have hD := twoContact_duplicates_lower mu delta hleft hright
  have hcost := mul_le_mul_of_nonneg_left hD (mul_nonneg h0 (hR.le.trans hRb))
  have hfloor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRb h0) hdelta
  have hS : (v-b)*(twoContactLaw mu).success ≤ v-R := by
    by_cases hbv : b ≤ v
    · have hh := mul_le_mul_of_nonneg_left (twoContactLaw mu).success_le_one (sub_nonneg.mpr hbv)
      nlinarith
    · have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hbv))
        (twoContactLaw mu).success_nonneg
      linarith
  have hEfloor : (t-R)*(1-q t) ≤ error q t R := by
    dsimp only [error]
    exact le_add_of_nonneg_right (integral_nonneg fun x => sub_nonneg.mpr (hq1 x))
  have hEvalue := mul_le_mul_of_nonneg_right (sub_le_sub_right hvt R) (sub_nonneg.mpr (hq1 t))
  rw [affine_zero_base_utility]
  nlinarith

theorem hidden_two_route_below_value {q : ℝ → ℝ} (hq1 : ∀ x, q x ≤ 1)
    {t R eta delta v b : ℝ} (hR : 0 < R) (hRt : R<t) (hvR : v ≤ R)
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hguard : error q t R<eta*R*(1-2*delta))
    (hRb : R ≤ b) (mu : FiniteLaw (Bool × Bool))
    (hleft : 1-delta ≤ mu.prob (fun z => z.1=true))
    (hright : 1-delta ≤ mu.prob (fun z => z.2=true)) (G : Schedule 2) :
    (twoContactLaw mu).utility v b 0 (Schedule.affine 2 eta h0 h1) G < 0 := by
  have hE := error_nonneg hRt.le hq1
  have hprod : 0 < eta*R*(1-2*delta) := hE.trans_lt hguard
  have hdelta : 0 ≤ 1-2*delta := by
    by_contra hbad
    have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h0 hR.le) (le_of_not_ge hbad)
    linarith
  have hD := twoContact_duplicates_lower mu delta hleft hright
  have hcost := mul_le_mul_of_nonneg_left hD (mul_nonneg h0 (hR.le.trans hRb))
  have hfloor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRb h0) hdelta
  have hS := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hvR.trans hRb))
    (twoContactLaw mu).success_nonneg
  rw [affine_zero_base_utility]
  nlinarith

end FCAppendix.Existence.RankEnvelope
