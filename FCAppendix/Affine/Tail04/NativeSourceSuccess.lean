import FCAppendix.Affine.Tail04.NativeSourceCountOutput
import FCAppendix.Affine.Tail04.BoundedSourceNativeInput
import FCAppendix.PayOnce.BroadcastRescue

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourceSuccess
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

lemma qR_nonneg : 0 ≤ s.scalar.qR := by
  unfold ScalarInput.qR
  exact div_nonneg (sub_nonneg.mpr ((div_le_one₀ s.scalar.floor_pos).mpr
    s.scalar.multiplier_below_floor.le)) s.scalar.xi_pos.le

lemma rho_le_one : s.scalar.rho ≤ 1 := by
  have hq := qR_nonneg s
  have hq1 := s.scalar.qR_lt_one
  have hs0 := s.scalar.mixedMass_pos
  have hs1 := s.scalar.mixedMass_lt_one
  have hsq : (1-s.scalar.qR)^2 ≤ 1 := by nlinarith
  unfold ScalarInput.rho
  nlinarith [sq_nonneg (1-s.scalar.qR)]

lemma demand_le_qR (b price : ℝ) (hb : 0 < b) (hR : b < s.scalar.R)
    (hp : s.scalar.lambdaLo ≤ price) :
    EqualCapacity.demand s.scalar.xi b price ≤ s.scalar.qR := by
  have hratio : s.scalar.lambdaLo/s.scalar.R ≤ price/b := by
    apply (div_le_div_iff₀ s.scalar.floor_pos hb).mpr
    nlinarith [s.scalar.multiplier_pos]
  have hraw : (1-price/b)/s.scalar.xi ≤ s.scalar.qR :=
    div_le_div_of_nonneg_right (by linarith) s.scalar.xi_pos.le
  exact max_le (qR_nonneg s) ((min_le_right _ _).trans hraw)

lemma mixed_failure_floor (q : ℝ) (_hq0 : 0 ≤ q) (hqR : q ≤ s.scalar.qR) :
    s.scalar.rho ≤ (1-s.scalar.ownerMass)*(1-q)^2 := by
  have hq1 := s.scalar.qR_lt_one
  have hsq : (1-s.scalar.qR)^2 ≤ (1-q)^2 := by nlinarith
  change s.scalar.mixedMass*(1-s.scalar.qR)^2 ≤ _
  have hh := mul_le_mul_of_nonneg_left hsq s.scalar.mixedMass_pos.le
  simpa only [ScalarInput.ownerMass,sub_sub_cancel] using hh

lemma success_le_broadcast {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (i : Fin m) (act : JointAction 2) :
    ((problem G i).outcome act).success ≤ ((problem G i).outcome (broadcastAction act)).success := by
  rw [problem_outcome,problem_outcome,CountLaw.success,CountLaw.success,
    CountLaw.expect_ofMeasure,CountLaw.expect_ofMeasure]
  apply integral_mono
    (CountLaw.integrable_comp (sampleLaw G) _ (measurable_focalCount G i act)
      (fun r => successIndicator r.val))
    (CountLaw.integrable_comp (sampleLaw G) _ (measurable_focalCount G i (broadcastAction act))
      (fun r => successIndicator r.val))
  intro omega
  exact successIndicator_mono_nat (focalCount_le_broadcast G i act omega)

variable {A : FrozenActiveFamily (NativeSource.input s hs)}
  (S : SourceFamily (NativeSource.input s hs) A)

include hs in
lemma finite_price_lower (k : ℕ) : s.scalar.lambdaLo ≤ S.price k := by
  rw [hs.lower_multiplier]
  have hq : (NativeSource.input s hs).qbar = 3/5 := NativeSource.exposure_eq s
  have h := (S.exceptionalReference_box k).1
  change (1-(NativeSource.input s hs).xi*(NativeSource.input s hs).qbar)*s.L ≤ S.price k at h
  rw [hq] at h
  change (1-s.scalar.xi*(3/5))*s.L ≤ S.price k at h
  exact h

theorem exists_success_error :
    ∃ err : ℕ → ℝ,(∀ k,0 < err k) ∧ Tendsto err atTop (nhds 0) ∧
      ∀ᶠ k in atTop,∀ (i : Fin (S.M k)) (act : JointAction 2),act.bid < s.scalar.R →
        ((problem (S.game k) i).outcome act).success ≤ 1-s.scalar.rho+err k := by
  obtain ⟨err,hpos,hnull,hevent⟩ := NativeSourceCountOutput.common_count_error S
  refine ⟨err,hpos,hnull,?_⟩
  filter_upwards [hevent] with k hk
  intro i act hR
  let br := broadcastAction act
  have hbR : br.bid < s.scalar.R := hR
  have hr : br.routeCount = 2 := rfl
  have hz := hk i br hr
  have htarget : s.scalar.rho-err k ≤ ((problem (S.game k) i).outcome br).mass 0 := by
    by_cases hlo : br.bid ≤ P.d0
    · have hb := (abs_lt.mp (hz.2.2 hlo)).1
      have hrho := rho_le_one s
      linarith
    · have hd : P.d0 < br.bid := lt_of_not_ge hlo
      have hbp : 0 < br.bid := P.d0_pos.trans hd
      let q := EqualCapacity.demand s.scalar.xi br.bid (S.price k)
      have hq0 : 0 ≤ q := le_max_left _ _
      have hqR : q ≤ s.scalar.qR := demand_le_qR s br.bid (S.price k) hbp hbR
        (finite_price_lower s hs S k)
      have hf := mixed_failure_floor s q hq0 hqR
      by_cases hbox : br.bid ∈ Icc s.L s.scalar.U
      · have hb := (abs_lt.mp (hz.1 hbox)).1
        change -err k < ((problem (S.game k) i).outcome br).mass 0-
          (1-s.scalar.ownerMass)*(1-q)^2 at hb
        linarith
      · have hb := (abs_lt.mp (hz.2.1 hd hbR hbox)).1
        have hmix : (1-s.scalar.ownerMass)*(1-q)^2 ≤ (1-q)^2 :=
          mul_le_of_le_one_left (sq_nonneg _) (by linarith [s.scalar.ownerMass_bounds.1])
        change -err k < ((problem (S.game k) i).outcome br).mass 0-(1-q)^2 at hb
        linarith
  have hmono := success_le_broadcast (S.game k) i act
  rw [two_count_zero_mass] at htarget
  linarith

end FCAppendix.Affine.Tail04.NativeSourceSuccess
