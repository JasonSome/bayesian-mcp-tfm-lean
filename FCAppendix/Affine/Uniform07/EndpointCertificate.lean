import FCAppendix.Affine.Uniform07.ObjectiveBounds
import FCAppendix.Affine.Uniform07.PureRateBounds
import FCAppendix.Affine.Uniform07.SourceAcceptance

namespace FCAppendix.Affine.Uniform07

theorem first_rate_low : (945861/6250000000000:ℝ) < canonicalRate .first (739/1000) :=
  first_test_objective.trans_le (test_below_canonical_rate .first
    (by norm_num [x,xQ]) (by norm_num : (0:ℝ)≤359/10000))

theorem second_rate_low : (5353363/25000000000000:ℝ) < canonicalRate .second (691/1000) :=
  second_test_objective.trans_le (test_below_canonical_rate .second
    (by norm_num [x,xQ]) (by norm_num : (0:ℝ)≤431/10000))

theorem canonical_lower_endpoint_gap :
    pureRate .first (739/1000)<canonicalRate .first (739/1000) ∧
    pureRate .second (691/1000)<canonicalRate .second (691/1000) := by
  constructor
  · linarith [first_pure_low,first_rate_low]
  · linarith [second_pure_low,second_rate_low]

theorem canonical_upper_endpoint_gap :
    canonicalRate .first (371/500)<pureRate .first (x .first) ∧
    canonicalRate .second (347/500)<pureRate .second (x .second) := by
  norm_num only [x,xQ,Rat.cast_div,Rat.cast_ofNat]
  constructor
  · linarith [first_rate_high,first_pure_entry]
  · linarith [second_rate_high,second_pure_entry]

theorem source_rate_endpoints :
    (945861/6250000000000:ℝ)<canonicalRate .first (739/1000) ∧
    pureRate .first (739/1000)<(2962933/25000000000000:ℝ) ∧
    canonicalRate .first (371/500)<(786282/10^13:ℝ) ∧
    (5364893/50000000000000:ℝ)<pureRate .first (3/4) ∧
    (5353363/25000000000000:ℝ)<canonicalRate .second (691/1000) ∧
    pureRate .second (691/1000)<(4136357/25000000000000:ℝ) ∧
    canonicalRate .second (347/500)<(935290/10^13:ℝ) ∧
    (123313/800000000000:ℝ)<pureRate .second (7/10) :=
  ⟨first_rate_low,first_pure_low,first_rate_high,first_pure_entry,
    second_rate_low,second_pure_low,second_rate_high,second_pure_entry⟩
end FCAppendix.Affine.Uniform07
