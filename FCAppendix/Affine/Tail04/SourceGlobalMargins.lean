import FCAppendix.Affine.Tail04.RouteMenuStatistics
import FCAppendix.Affine.Tail04.SourceMomentRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceGlobalMargins
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuPopulation SourceMenuIdentity SourceMomentRectangle
open GlobalLower RouteMenuStatistics UnusedFocalCountError

def multiplierFloor (ξ : ℝ) : ℝ := 1-19*ξ/20-ξ/250

lemma multiplierFloor_bounds {ξ : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2) :
    1/2≤ multiplierFloor ξ ∧ multiplierFloor ξ≤1 := by
  unfold multiplierFloor
  constructor <;> linarith

lemma singleton_cost_gap {ξ : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2) :
    Central.B ξ+ξ/40≤ multiplierFloor ξ/(1-ξ) := by
  have hk : 0<1-ξ := by linarith
  apply (le_div_iff₀ hk).mpr
  unfold multiplierFloor Central.B
  nlinarith [sq_nonneg ξ]

lemma broadcast_cost_gap {ξ v : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2) (hv : 100≤ v) :
    Central.B ξ+1/50≤2*multiplierFloor ξ-(multiplierFloor ξ)^2/v := by
  have hlo:=multiplierFloor_bounds hξ hξh
  have hv0 : 0< v := by linarith
  have hsq : (multiplierFloor ξ)^2≤1 := by nlinarith
  have hfrac : (multiplierFloor ξ)^2/v≤1/100 :=
    (div_le_iff₀ hv0).mpr (by nlinarith)
  unfold Central.B multiplierFloor at *
  linarith

lemma large_value_threshold {ξ v : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2) (hv : 100≤ v) :
    multiplierFloor ξ/(1-ξ)^2≤ v := by
  have hlo:=multiplierFloor_bounds hξ hξh
  have hk : 0<1-ξ := by linarith
  have hs : 1/4≤(1-ξ)^2 := by nlinarith
  exact (div_le_div_of_nonneg_left (by linarith [hlo.1]) (by norm_num : (0:ℝ)<1/4) hs).trans
    (by nlinarith [hlo.2])

variable (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (hξh : ξ<1/2)
  (hθ : P.theta≤ ξ/100) (hw : P.w≤ ξ/1000)
  (hvA : P.vA=11*ξ/(10*P.theta))

include hξ hξh hθ hw hvA in
lemma active_value_large : 100≤ P.vA-P.w := by
  have hlarge : 110≤ P.vA := by
    rw [hvA]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<10) P.theta_pos)).mpr
    nlinarith
  linarith

include hξ hξh hθ hw hvA in
theorem active_partial_gap {v : ℝ} (hv : P.vA-P.w≤ v) :
    ξ/8≤ P.theta*v+(1-P.theta)*Central.R ξ-Central.B ξ := by
  have hsource:=source_active_partial_margin ξ P.theta P.theta_pos.ne'
  rw [←hvA] at hsource
  have hR : Central.R ξ≤1 := by unfold Central.R;linarith
  have hR0 : 0≤ Central.R ξ := by unfold Central.R;linarith
  have hw1 : P.w≤1/100 := by linarith
  have htw : P.theta*P.w≤ ξ/10000 := by
    calc
      _≤ P.theta*(1/100) := mul_le_mul_of_nonneg_left hw1 P.theta_pos.le
      _≤(ξ/100)*(1/100) := mul_le_mul_of_nonneg_right hθ (by norm_num)
      _=_ := by ring
  have htr : P.theta*Central.R ξ≤ ξ/100 := by
    have hh:=mul_le_mul_of_nonneg_left hR P.theta_pos.le
    linarith
  have hv' := mul_le_mul_of_nonneg_left hv P.theta_pos.le
  unfold Central.R Central.B at *
  nlinarith

include hξ hξh hθ in
theorem partial_singleton_margin :
    1+9*ξ/10≤(2-Central.R ξ)*(1-P.theta) := by
  have ht : P.theta≤1/200 := by linarith
  have ht' : P.theta≤(200:ℝ)⁻¹ := by simpa only [one_div] using! ht
  have hprod : ξ*P.theta≤ ξ/200 := by
    simpa only [div_eq_mul_inv] using! mul_le_mul_of_nonneg_left ht' hξ.le
  unfold Central.R
  nlinarith

include hξ hξh hθ in
theorem partial_broadcast_canonical_margin :
    1/3≤2*multiplierFloor ξ-(multiplierFloor ξ)^2/2-
      (Central.R ξ+P.theta*(2-Central.R ξ)) := by
  have hsq : ξ^2≤1/4 := by nlinarith
  have ht : P.theta≤1/200 := by linarith
  have hR : 0≤ Central.R ξ := by unfold Central.R;linarith
  have hprod : P.theta*(2-Central.R ξ)≤1/100 := by
    have hh:=mul_le_mul_of_nonneg_left (show 2-Central.R ξ≤2 by linarith) P.theta_pos.le
    nlinarith
  unfold multiplierFloor Central.R at *
  nlinarith

include hξ hξh hθ hw in
theorem partial_high_price_gap {v : ℝ} (hv : v∈Icc (2-P.w) (2+P.w)) :
    ξ/2≤(v-Central.R ξ)*(1-P.theta)-(v-1) := by
  have hc:=partial_singleton_margin P hξ hξh hθ
  have hvw : |v-2|≤ P.w := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have ht : 0≤1-P.theta := by linarith [P.theta_small]
  have hs:=mul_le_mul_of_nonneg_left (abs_le.mp hvw).1 ht
  have hs' := mul_le_mul_of_nonneg_left (abs_le.mp hvw).2 P.theta_pos.le
  nlinarith [P.theta_pos,P.w_pos,P.theta_small]

lemma accept_flag_small : baseFlag P false≤1/10 := by
  have ha : 66/100≤ activeMass P.theta := by
    unfold activeMass delta
    nlinarith [P.theta_pos,P.theta_small]
  change 10*P.theta^2/(9*activeMass P.theta)≤1/10
  apply (div_le_iff₀ (mul_pos (by norm_num) P.active_mass_pos)).mpr
  nlinarith [P.theta_pos,P.theta_small]

include hξ in
theorem active_singleton_marginal {b qA qR : ℝ}
    (hb : b∈Icc (1:ℝ) (Central.B ξ)) (hqA : qA≤1) (hqR : qR≤1) :
    (1-P.theta)*((1-mixedProbability P ξ false b)/2+mixedProbability P ξ false b*qA)+
      P.theta*((1-mixedProbability P ξ true b)/2+mixedProbability P ξ true b*qR)≤3/5 := by
  have heA:=mixedProbability_bounds P hξ hb false
  have heR:=mixedProbability_bounds P hξ hb true
  have heAsmall : mixedProbability P ξ false b≤1/10 :=
    (bid_mixed_flag_le_baseline (Central.B ξ) b (baseFlag P false)
      (by unfold Central.B;linarith) hb.1 hb.2 (baseFlag_bounds P false).1.le).trans
        (accept_flag_small P)
  have hm:=active_two_regime_one_marginal P.theta _ _ qA qR P.theta_pos.le
    (by linarith [P.theta_small]) heA.1 heR.1 hqA hqR
  have ha:=mul_le_mul_of_nonneg_left heAsmall (show 0≤1-P.theta by linarith [P.theta_small])
  have hr:=mul_le_mul_of_nonneg_left heR.2 P.theta_pos.le
  nlinarith [P.theta_small]

include hξ hξh hθ hw hvA in
theorem active_singleton_gap {v : ℝ} (hv : P.vA-P.w≤ v) :
    1≤ v-Central.B ξ-(3/5)*v := by
  have hv100:=(active_value_large P hξ hξh hθ hw hvA).trans hv
  unfold Central.B
  linarith

end FCAppendix.Affine.Tail04.SourceGlobalMargins
