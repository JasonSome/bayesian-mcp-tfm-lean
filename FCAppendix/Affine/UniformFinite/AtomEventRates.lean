import FCAppendix.Affine.LowBody.CategoricalRateGuards
import FCAppendix.Affine.LowBody.ArrivalUnderflow
import FCAppendix.Affine.Uniform07.Parameters

noncomputable section

namespace FCAppendix.Affine.UniformFinite.AtomEvents

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

local notation "c" => Uniform07.capacity
local notation "ρ" => Uniform07.rho
local notation "δ" => Uniform07.delta

def otherLower (m : ℕ) : ℕ := m - 2 * c m - 2

def lowerEvent (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) : ℝ :=
  (IndependentCounts.binomial (m-1) ((1+t)/2)
    (by linarith) (by linarith)).prob (fun k => k.val ≤ c m-1)

def boundaryEvent (t : ℝ) (m : ℕ) : ℝ :=
  PiBinomial.pmf (m-2) t (otherLower m) *
    PiBinomial.pmf (2*c m) (1/2) (c m-otherLower m-1)

def duplicateEvent (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (m : ℕ) : ℝ :=
  (IndependentCounts.binomial (m-2) z hz0 hz1).prob
    (fun k => m-2*c m ≤ k.val)

def sourceCoefficient (η χ t z : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (m : ℕ) : ℝ :=
  4*η*((m-1:ℕ):ℝ)*duplicateEvent z hz0 hz1 m /
    ((1-χ)*lowerEvent t ht0 ht1 m*boundaryEvent t m)

def lowerRate (t : ℝ) : ℝ := Ample.binaryKL ρ ((1+t)/2)
def boundaryRate (t : ℝ) : ℝ :=
  Ample.binaryKL δ t + (1-δ)*
    Ample.binaryKL (1/2-δ/(1-δ)) (1/2)
def duplicateRate (z : ℝ) : ℝ := Ample.binaryKL δ z

theorem actual_lower_arrival_probability (t : ℝ) (ht0 : 0≤ t) (ht1 : t≤1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (m : ℕ) (hc : 0< c m) :
    (CommonList.iid (LowBody.categoryLaw t 0 (1-t) ht0 (by norm_num)
      (by linarith) (by ring) G) (m-1)).prob (LowBody.LocalUnderflow (c m) 0) =
      lowerEvent t ht0 ht1 m := by
  have hh := LowBody.localUnderflow_probability t 0 (1-t) ht0 (by norm_num)
    (by linarith) (by ring) G (m-1) (c m) hc
  have hp : 1-(1-t)/2=(1+t)/2 := by ring
  simpa only [hp,lowerEvent] using hh

theorem fair_boundary_mass_lower (capacity N k : ℕ) (hk : k≤ N) :
    PiBinomial.pmf (2*capacity) (1/2) (capacity-N-1) ≤
      PiBinomial.pmf (2*capacity) (1/2) (capacity-k-1) := by
  have hKN : capacity-k-1≤2*capacity := by omega
  have hKc : ((capacity-k-1:ℕ):ℝ)≤ capacity := Nat.cast_le.mpr (by omega)
  have hmode : ((capacity-k-1:ℕ):ℝ)≤((2*capacity+1:ℕ):ℝ)*(1/2) := by
    push_cast
    linarith
  exact LowBody.pmf_le_boundary (2*capacity) (capacity-k-1) (1/2) (by norm_num)
    (by norm_num) hKN hmode (capacity-N-1) (by omega)

lemma pmf_le_one (N K : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hKN : K ≤ N) : PiBinomial.pmf N p K ≤ 1 := by
  let μ := IndependentCounts.binomial N p hp0 hp1
  let k : Fin (N+1) := ⟨K,by omega⟩
  have hh := μ.prob_le_one (fun r => r=k)
  simpa only [FiniteLaw.prob_eq_expect,FiniteLaw.expect_singleton,
    μ,k,PiBinomial.binomial_mass] using hh

lemma log_pmf_entropy_upper (N K : ℕ) (p : ℝ)
    (hK0 : 0< K) (hKN : K< N) (hp0 : 0< p) (hp1 : p<1) :
    log (PiBinomial.pmf N p K) ≤
      -(N:ℝ)*Ample.binaryKL ((K:ℝ)/N) p := by
  have hN : (0:ℝ)< N := Nat.cast_pos.mpr (hK0.trans hKN)
  have hq0 : 0≤(K:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hN.le
  have hq1 : (K:ℝ)/N≤1 :=
    ((div_lt_one hN).mpr (Nat.cast_lt.mpr hKN)).le
  have hmass := LowBody.pmf_pos N K ((K:ℝ)/N)
    (div_pos (Nat.cast_pos.mpr hK0) hN)
    ((div_lt_one hN).mpr (Nat.cast_lt.mpr hKN)) hKN.le
  have hlog := Real.log_le_log hmass (pmf_le_one N K ((K:ℝ)/N) hq0 hq1 hKN.le)
  rw [Real.log_one] at hlog
  rw [LowBody.log_pmf_change_parameter N K p hK0 hKN hp0 hp1]
  linarith

lemma log_card_div_tendsto_zero (N : ℕ→ℕ) (γ : ℝ)
    (hN : Tendsto N atTop atTop)
    (hNm : Tendsto (fun m => (N m:ℝ)/(m:ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun m => log ((N m+1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m => log ((N m+1:ℕ):ℝ)/(N m:ℝ)) atTop (𝓝 0) := by
    have hadd : Tendsto (fun m => (N m:ℝ)+1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hN).atTop_add
        (tendsto_const_nhds (x:=(1:ℝ)))
    have he := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hadd
    convert! he using 1; simp [Function.comp_def]
  have hh := hlog.mul hNm
  have heq : (fun m => log ((N m+1:ℕ):ℝ)/(N m:ℝ)*((N m:ℝ)/(m:ℝ))) =ᶠ[atTop]
      (fun m => log ((N m+1:ℕ):ℝ)/(m:ℝ)) := by
    filter_upwards [hN.eventually_gt_atTop 0] with m hm
    have hN0 : (N m:ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
    field_simp
  simpa only [zero_mul] using hh.congr' heq

theorem log_rate_of_boundary_sandwich (N K : ℕ→ℕ) (p q γ : ℝ)
    (hp0 : 0< p) (hp1 : p<1) (hq0 : 0< q) (hq1 : q<1)
    (hN : Tendsto N atTop atTop)
    (hNm : Tendsto (fun m => (N m:ℝ)/(m:ℝ)) atTop (𝓝 γ))
    (hKN : Tendsto (fun m => (K m:ℝ)/(N m:ℝ)) atTop (𝓝 q))
    (F : ℕ→ℝ)
    (hF : ∀ᶠ m in atTop, PiBinomial.pmf (N m) p (K m) ≤ F m ∧
      F m ≤ ((N m+1:ℕ):ℝ)*PiBinomial.pmf (N m) p (K m)) :
    Tendsto (fun m => -log (F m)/(m:ℝ)) atTop
      (𝓝 (γ*Ample.binaryKL q p)) := by
  have hlog := log_card_div_tendsto_zero N γ hN hNm
  have hKL := (LowBody.continuousAt_binaryKL_left p q hp0 hp1 hq0 hq1).tendsto.comp hKN
  have hmain := hNm.mul hKL
  have hlo : Tendsto (fun m => (N m:ℝ)/(m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p -
      log ((N m+1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 (γ*Ample.binaryKL q p)) := by
    simpa using hmain.sub hlog
  have hup : Tendsto (fun m => (N m:ℝ)/(m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p +
      log ((N m+1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 (γ*Ample.binaryKL q p)) := by
    simpa using hmain.add hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [hF,hN.eventually_gt_atTop 0,hKN.eventually_const_lt hq0,
      hKN.eventually_lt_const hq1,eventually_gt_atTop (0:ℕ)] with m hFm hNm0 hK0 hK1 hm0
    have hNR : (0:ℝ)< N m := Nat.cast_pos.mpr hNm0
    have hKNat : 0< K m := Nat.cast_pos.mp ((div_pos_iff_of_pos_right hNR).mp hK0)
    have hKlt : K m< N m := Nat.cast_lt.mp ((div_lt_one hNR).mp hK1)
    have hmass := LowBody.pmf_pos (N m) (K m) p hp0 hp1 hKlt.le
    have hFp : 0< F m := hmass.trans_le hFm.1
    have hlg := Real.log_le_log hFp hFm.2
    rw [Real.log_mul (by positivity) hmass.ne'] at hlg
    have hu := log_pmf_entropy_upper (N m) (K m) p hKNat hKlt hp0 hp1
    have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm0
    have hb : (N m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p -
        log ((N m+1:ℕ):ℝ) ≤ -log (F m) := by linarith
    have hh := div_le_div_of_nonneg_right hb hmR.le
    convert! hh using 1; ring
  · filter_upwards [hF,hN.eventually_gt_atTop 0,hKN.eventually_const_lt hq0,
      hKN.eventually_lt_const hq1,eventually_gt_atTop (0:ℕ)] with m hFm hNm0 hK0 hK1 hm0
    have hNR : (0:ℝ)< N m := Nat.cast_pos.mpr hNm0
    have hKNat : 0< K m := Nat.cast_pos.mp ((div_pos_iff_of_pos_right hNR).mp hK0)
    have hKlt : K m< N m := Nat.cast_lt.mp ((div_lt_one hNR).mp hK1)
    have hmass := LowBody.pmf_pos (N m) (K m) p hp0 hp1 hKlt.le
    have hlg := Real.log_le_log hmass hFm.1
    have hl := LowBody.log_pmf_entropy_lower (N m) (K m) p hKNat hKlt hp0 hp1
    have hmR : (0:ℝ)< m := Nat.cast_pos.mpr hm0
    have hb : -log (F m) ≤ (N m:ℝ)*Ample.binaryKL ((K m:ℝ)/N m) p +
        log ((N m+1:ℕ):ℝ) := by linarith
    have hh := div_le_div_of_nonneg_right hb hmR.le
    convert! hh using 1; ring

theorem pmf_log_rate (N K : ℕ→ℕ) (p q γ : ℝ)
    (hp0 : 0< p) (hp1 : p<1) (hq0 : 0< q) (hq1 : q<1)
    (hN : Tendsto N atTop atTop)
    (hNm : Tendsto (fun m => (N m:ℝ)/(m:ℝ)) atTop (𝓝 γ))
    (hKN : Tendsto (fun m => (K m:ℝ)/(N m:ℝ)) atTop (𝓝 q)) :
    Tendsto (fun m => -log (PiBinomial.pmf (N m) p (K m))/(m:ℝ))
      atTop (𝓝 (γ*Ample.binaryKL q p)) := by
  apply log_rate_of_boundary_sandwich N K p q γ hp0 hp1 hq0 hq1 hN hNm hKN _
  exact Eventually.of_forall (fun m => ⟨le_rfl,by
    have hmass : 0≤ PiBinomial.pmf (N m) p (K m) := by
      unfold PiBinomial.pmf
      positivity
    have hn : (1:ℝ)≤((N m+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hmass⟩)

lemma upper_tail_le_boundary (N K : ℕ) (p : ℝ)
    (hp0 : 0≤ p) (hp1 : p<1) (_hKN : K≤ N)
    (hmode : ((N+1:ℕ):ℝ)*p≤ K) :
    (IndependentCounts.binomial N p hp0 hp1.le).prob (fun r => K≤ r.val) ≤
      ((N+1:ℕ):ℝ)*PiBinomial.pmf N p K := by
  have hchain : ∀j,K≤ j→ j≤ N→ PiBinomial.pmf N p j≤ PiBinomial.pmf N p K := by
    intro j
    induction j with
    | zero =>
      intro hKj _
      have hK : K=0 := by omega
      simp [hK]
    | succ j ih =>
      intro hKj hjN
      by_cases he : j+1=K
      · rw [he]
      · have hKj' : K≤ j := by omega
        have hm : ((N+1:ℕ):ℝ)*p≤((j+1:ℕ):ℝ) :=
          hmode.trans (Nat.cast_le.mpr (by omega))
        exact (LowBody.pmf_next_le N j p hp0 hp1 (by omega) hm).trans (ih hKj' (by omega))
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  calc
    _ ≤ ∑ _r : Fin (N+1), PiBinomial.pmf N p K := by
      apply Finset.sum_le_sum
      intro r _
      rw [PiBinomial.binomial_mass]
      by_cases hr : K≤ r.val
      · simpa only [if_pos hr,mul_one] using hchain r.val hr (by omega)
      · simp only [if_neg hr,mul_zero]
        unfold PiBinomial.pmf
        positivity
    _ = _ := by simp

lemma pmf_le_upper_tail (N K : ℕ) (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1)
    (hKN : K≤ N) : PiBinomial.pmf N p K ≤
      (IndependentCounts.binomial N p hp0 hp1).prob (fun r => K≤ r.val) := by
  let μ := IndependentCounts.binomial N p hp0 hp1
  let k : Fin (N+1) := ⟨K,by omega⟩
  have hh := μ.prob_mono (E:=fun r => r=k) (F:=fun r => K≤ r.val)
    (by intro r hr; subst r; exact le_rfl)
  simpa only [FiniteLaw.prob_eq_expect,FiniteLaw.expect_singleton,
    μ,k,PiBinomial.binomial_mass] using hh

lemma capacity_brackets (m : ℕ) :
    (c m:ℝ) ≤ ρ*(m:ℝ) ∧ ρ*(m:ℝ)-1 < c m := by
  have hdiv := Nat.mod_add_div (999*m) 2000
  have hmod := Nat.mod_lt (999*m) (by norm_num : 0<2000)
  have hu : 2000*c m≤999*m := by dsimp [Uniform07.capacity]; omega
  have hl : 999*m<2000*(c m+1) := by dsimp [Uniform07.capacity]; omega
  have huR : (2000:ℝ)*(c m:ℝ)≤999*(m:ℝ) := by exact_mod_cast hu
  have hlR : (999:ℝ)*(m:ℝ)<2000*((c m:ℝ)+1) := by exact_mod_cast hl
  dsimp [Uniform07.rho]
  constructor <;> linarith

theorem capacity_fraction :
    Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ) := by
  have hlo : Tendsto (fun m : ℕ => ρ-1/(m:ℝ)) atTop (𝓝 ρ) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
    have hh := div_le_div_of_nonneg_right (capacity_brackets m).2.le hmR.le
    convert! hh using 1; field_simp
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
    exact (div_le_iff₀ hmR).mpr (by simpa only [mul_comm] using (capacity_brackets m).1)

theorem capacity_tendsto : Tendsto c atTop atTop := by
  refine tendsto_atTop.2 (fun K => ?_)
  filter_upwards [eventually_ge_atTop (3*K+3)] with m hm
  have hl := (capacity_brackets m).2
  have hmR : ((3*K+3:ℕ):ℝ)≤ m := Nat.cast_le.mpr hm
  have hK0 : (0:ℝ)≤ K := Nat.cast_nonneg K
  dsimp [Uniform07.rho] at hl
  have hKR : (K:ℝ)≤ c m := by push_cast at hmR; linarith
  exact Nat.cast_le.mp hKR

theorem eventually_count_geometry : ∀ᶠ m : ℕ in atTop,
    2*c m+2≤ m ∧ 0< otherLower m ∧ otherLower m+1< c m ∧ c m< m := by
  filter_upwards [eventually_ge_atTop (10000:ℕ)] with m hm
  obtain ⟨hu,hl⟩ := capacity_brackets m
  dsimp [Uniform07.rho] at hu hl
  have hmR : (10000:ℝ)≤ m := Nat.cast_le.mpr hm
  have hroomR : (2:ℝ)*(c m:ℝ)+3≤ m := by linarith
  have hroom : 2*c m+3≤ m := by exact_mod_cast hroomR
  have hother : otherLower m=m-2*c m-2 := rfl
  have hcM : c m< m := Nat.cast_lt.mp (by linarith : (c m:ℝ)< m)
  have hroom' : m+2<3*c m := by
    have hR : (m:ℝ)+2<3*(c m:ℝ) := by linarith
    exact_mod_cast hR
  dsimp [otherLower]
  omega

theorem first_copy_category_geometry (m k : ℕ)
    (hroom : 2*c m+2≤ m) (hlower : otherLower m+1< c m)
    (hk : k≤ otherLower m) :
    let H₀ := c m-k-1
    let H₁ := 2*c m-H₀
    otherLower m+H₀+H₁=m-2 ∧ H₀+k=c m-1 ∧
      c m< H₁ ∧ c m-H₀=k+1 ∧ c m-H₁=0 := by
  dsimp only
  have hN : otherLower m=m-2*c m-2 := rfl
  omega

theorem otherLower_fraction :
    Tendsto (fun m => (otherLower m:ℝ)/(m:ℝ)) atTop (𝓝 δ) := by
  have hh : Tendsto (fun m : ℕ => 1-2*((c m:ℝ)/(m:ℝ))-2/(m:ℝ))
      atTop (𝓝 (1-2*ρ)) := by
    simpa using (tendsto_const_nhds.sub (capacity_fraction.const_mul 2)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ))
  have hident : 1-2*ρ=δ := by norm_num [Uniform07.rho,Uniform07.delta]
  rw [hident] at hh
  apply hh.congr'
  filter_upwards [eventually_count_geometry,eventually_gt_atTop (0:ℕ)] with m hm hm0
  have hmc : 2*c m≤ m := by omega
  have hm2 : 2≤ m-2*c m := by omega
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm0).ne'
  dsimp [otherLower]
  rw [Nat.cast_sub hm2,Nat.cast_sub hmc]
  push_cast
  field_simp

theorem otherLower_trials_fraction :
    Tendsto (fun m => (otherLower m:ℝ)/((m-2:ℕ):ℝ)) atTop (𝓝 δ) := by
  have hh := otherLower_fraction.div (LowBody.tendsto_trials_fraction 2) one_ne_zero
  have hh' : Tendsto (fun m => ((otherLower m:ℝ)/(m:ℝ))/(((m-2:ℕ):ℝ)/(m:ℝ)))
      atTop (𝓝 δ) := by convert! hh using 1; first | rfl | simp
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm).ne'
  field_simp

theorem fair_trials_fraction :
    Tendsto (fun m => ((2*c m:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 (1-δ)) := by
  convert! capacity_fraction.const_mul 2 using 1 <;>
    simp [Uniform07.rho,Uniform07.delta] <;> ring

theorem fair_boundary_fraction :
    Tendsto (fun m => ((c m-otherLower m-1:ℕ):ℝ)/((2*c m:ℕ):ℝ))
      atTop (𝓝 (1/2-δ/(1-δ))) := by
  have hnum : Tendsto (fun m => ((c m-otherLower m-1:ℕ):ℝ)/(m:ℝ))
      atTop (𝓝 (ρ-δ)) := by
    have hh := (capacity_fraction.sub otherLower_fraction).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    have hh' : Tendsto (fun m : ℕ => (c m:ℝ)/(m:ℝ)-(otherLower m:ℝ)/(m:ℝ)-1/(m:ℝ))
        atTop (𝓝 (ρ-δ)) := by simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_count_geometry] with m hm
    rw [Nat.cast_sub (show 1≤ c m-otherLower m by omega),
      Nat.cast_sub (show otherLower m≤ c m by omega)]
    push_cast
    ring
  have hh := hnum.div fair_trials_fraction (by norm_num [Uniform07.delta] : 1-δ≠0)
  have he : (ρ-δ)/(1-δ)=1/2-δ/(1-δ) := by norm_num [Uniform07.rho,Uniform07.delta]
  rw [he] at hh
  change Tendsto (fun m => ((c m-otherLower m-1:ℕ):ℝ)/(m:ℝ)/
    (((2*c m:ℕ):ℝ)/(m:ℝ))) atTop (𝓝 (1/2-δ/(1-δ))) at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm).ne'
  field_simp

theorem duplicate_threshold_trials_fraction :
    Tendsto (fun m => ((m-2*c m:ℕ):ℝ)/((m-2:ℕ):ℝ)) atTop (𝓝 δ) := by
  have hnum : Tendsto (fun m => ((m-2*c m:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 δ) := by
    have hh := otherLower_fraction.add (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ))
    have hh' : Tendsto (fun m => (otherLower m:ℝ)/(m:ℝ)+2/(m:ℝ)) atTop (𝓝 δ) := by
      simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_count_geometry] with m hm
    have hhe : otherLower m+2=m-2*c m := by dsimp [otherLower]; omega
    have hheR := congrArg (fun n : ℕ => (n:ℝ)) hhe
    push_cast at hheR
    rw [← hheR]
    ring
  have hh := hnum.div (LowBody.tendsto_trials_fraction 2) one_ne_zero
  have hh' : Tendsto (fun m => (((m-2*c m:ℕ):ℝ)/(m:ℝ))/(((m-2:ℕ):ℝ)/(m:ℝ)))
      atTop (𝓝 δ) := by convert! hh using 1; first | rfl | simp
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm).ne'
  field_simp

theorem literal_L_log_rate (t : ℝ) (ht0 : 0< t) (ht1 : t<1) :
    Tendsto (fun m => -log (lowerEvent t ht0.le ht1.le m)/(m:ℝ))
      atTop (𝓝 (lowerRate t)) := by
  let p : ℝ := (1+t)/2
  have hp0 : 0< p := by dsimp [p]; linarith
  have hp1 : p<1 := by dsimp [p]; linarith
  have hρ0 : 0<ρ := by norm_num [Uniform07.rho]
  have hρ1 : ρ<1 := by norm_num [Uniform07.rho]
  have hρp : ρ< p := by dsimp [p,Uniform07.rho]; linarith
  have hKN := LowBody.tendsto_boundary_trials_fraction c ρ hρ0 capacity_fraction 1
  have hh := log_rate_of_boundary_sandwich (fun m => m-1) (fun m => c m-1) p ρ 1
    hp0 hp1 hρ0 hρ1 (tendsto_sub_atTop_nat 1)
    (LowBody.tendsto_trials_fraction 1) hKN (lowerEvent t ht0.le ht1.le) ?_
  · simpa only [one_mul,lowerRate,p] using hh
  have hmode := (LowBody.tendsto_boundary_fraction c ρ hρ0 capacity_fraction).eventually_lt_const hρp
  filter_upwards [hmode,eventually_count_geometry,eventually_gt_atTop (0:ℕ)] with m hm hgeom hm0
  have hKNat : c m-1≤ m-1 := by omega
  have hmR : (0:ℝ)< m := Nat.cast_pos.mpr hm0
  have hmodeR : ((c m-1:ℕ):ℝ)≤(((m-1)+1:ℕ):ℝ)*p := by
    have he : m-1+1=m := by omega
    rw [he]
    simpa only [mul_comm] using ((div_lt_iff₀ hmR).mp hm).le
  exact ⟨LowBody.pmf_le_lower_tail (m-1) (c m-1) p hp0.le hp1.le hKNat,
    LowBody.binomial_tail_le_boundary (m-1) (c m-1) p hp0.le hp1 hKNat hmodeR⟩

theorem literal_H_log_rate (t : ℝ) (ht0 : 0< t) (ht1 : t<1) :
    Tendsto (fun m => -log (boundaryEvent t m)/(m:ℝ))
      atTop (𝓝 (boundaryRate t)) := by
  have hδ0 : 0<δ := by norm_num [Uniform07.delta]
  have hδ1 : δ<1 := by norm_num [Uniform07.delta]
  have hfirst := pmf_log_rate (fun m => m-2) otherLower t δ 1
    ht0 ht1 hδ0 hδ1 (tendsto_sub_atTop_nat 2)
    (LowBody.tendsto_trials_fraction 2) otherLower_trials_fraction
  have hN : Tendsto (fun m => 2*c m) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [capacity_tendsto.eventually_ge_atTop K] with m hm
    omega
  have hsecond := pmf_log_rate (fun m => 2*c m) (fun m => c m-otherLower m-1)
    (1/2) (1/2-δ/(1-δ)) (1-δ) (by norm_num) (by norm_num)
    (by norm_num [Uniform07.delta]) (by norm_num [Uniform07.delta])
    hN fair_trials_fraction fair_boundary_fraction
  have hh := hfirst.add hsecond
  have hh' : Tendsto (fun m => -log (PiBinomial.pmf (m-2) t (otherLower m))/(m:ℝ) +
      -log (PiBinomial.pmf (2*c m) (1/2) (c m-otherLower m-1))/(m:ℝ))
      atTop (𝓝 (boundaryRate t)) := by simpa only [one_mul,boundaryRate] using hh
  apply hh'.congr'
  filter_upwards [eventually_count_geometry] with m hm
  have hfirstp := LowBody.pmf_pos (m-2) (otherLower m) t ht0 ht1 (by dsimp [otherLower]; omega)
  have hsecondp := LowBody.pmf_pos (2*c m) (c m-otherLower m-1) (1/2)
    (by norm_num) (by norm_num) (by omega)
  rw [boundaryEvent,Real.log_mul hfirstp.ne' hsecondp.ne']
  ring

theorem literal_E_log_rate (z : ℝ) (hz0 : 0< z) (hzδ : z<δ) :
    Tendsto (fun m => -log (duplicateEvent z hz0.le
      (hzδ.trans (by norm_num [Uniform07.delta] : δ<1)).le m)/(m:ℝ))
      atTop (𝓝 (duplicateRate z)) := by
  have hz1 : z<1 := hzδ.trans (by norm_num [Uniform07.delta])
  have hδ0 : 0<δ := by norm_num [Uniform07.delta]
  have hδ1 : δ<1 := by norm_num [Uniform07.delta]
  have hh := log_rate_of_boundary_sandwich (fun m => m-2) (fun m => m-2*c m)
    z δ 1 hz0 hz1 hδ0 hδ1 (tendsto_sub_atTop_nat 2)
    (LowBody.tendsto_trials_fraction 2) duplicate_threshold_trials_fraction
    (duplicateEvent z hz0.le hz1.le) ?_
  · simpa only [one_mul,duplicateRate] using hh
  have hmean : Tendsto (fun m : ℕ => ((((m-2)+1:ℕ):ℝ)/((m-2:ℕ):ℝ))*z)
      atTop (𝓝 z) := by
    have hbase : Tendsto (fun m : ℕ => (1:ℝ)+1/((m-2:ℕ):ℝ)) atTop (𝓝 1) := by
      have hh := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ) |>.comp (tendsto_sub_atTop_nat 2)
      simpa using tendsto_const_nhds.add hh
    have he := hbase.mul_const z
    have he' : Tendsto (fun m : ℕ => ((1:ℝ)+1/((m-2:ℕ):ℝ))*z) atTop (𝓝 z) := by simpa using he
    apply he'.congr'
    filter_upwards [eventually_gt_atTop (2:ℕ)] with m hm
    have hnR : ((m-2:ℕ):ℝ)≠0 := (Nat.cast_pos.mpr (by omega : 0< m-2)).ne'
    push_cast
    field_simp
  have hmode := (duplicate_threshold_trials_fraction.sub hmean).eventually_const_lt
    (sub_pos.mpr hzδ)
  filter_upwards [hmode,eventually_count_geometry,capacity_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop (2:ℕ)] with m hm hgeom hc1 hm2
  have hN : (0:ℝ)<((m-2:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hK : m-2*c m≤ m-2 := by omega
  have hmodeR : ((((m-2)+1:ℕ):ℝ))*z≤((m-2*c m:ℕ):ℝ) := by
    have he : ((((m-2)+1:ℕ):ℝ)/((m-2:ℕ):ℝ))*z=
        ((((m-2)+1:ℕ):ℝ))*z/((m-2:ℕ):ℝ) := by ring
    rw [he] at hm
    exact ((div_lt_div_iff_of_pos_right hN).mp (by linarith :
      ((((m-2)+1:ℕ):ℝ))*z/((m-2:ℕ):ℝ) < ((m-2*c m:ℕ):ℝ)/((m-2:ℕ):ℝ))).le
  exact ⟨pmf_le_upper_tail (m-2) (m-2*c m) z hz0.le hz1.le hK,
    upper_tail_le_boundary (m-2) (m-2*c m) z hz0.le hz1 hK hmodeR⟩

theorem boundaryEvent_formula (t : ℝ) (m : ℕ)
    (hK : c m-otherLower m-1≤2*c m) :
    boundaryEvent t m = PiBinomial.pmf (m-2) t (otherLower m) *
      (2:ℝ)^(-((2*c m:ℕ):ℤ)) * ((2*c m).choose (c m-otherLower m-1):ℝ) := by
  have hpow : (1/2:ℝ)^(c m-otherLower m-1) *
      (1/2:ℝ)^(2*c m-(c m-otherLower m-1)) = (1/2:ℝ)^(2*c m) := by
    rw [← pow_add,Nat.add_sub_of_le hK]
  change PiBinomial.pmf (m-2) t (otherLower m) *
    (((2*c m).choose (c m-otherLower m-1):ℝ) *
      (1/2:ℝ)^(c m-otherLower m-1) *
      (1-(1/2:ℝ))^(2*c m-(c m-otherLower m-1))) = _
  rw [show (1:ℝ)-1/2=1/2 by norm_num,
    mul_assoc _ ((1/2:ℝ)^_) _,hpow]
  have he : (1/2:ℝ)^(2*c m)=(2:ℝ)^(-((2*c m:ℕ):ℤ)) := by
    rw [zpow_neg]
    change (1/2:ℝ)^(2*c m)=((2:ℝ)^(2*c m))⁻¹
    simp only [one_div, inv_pow]
  rw [he]
  ring

theorem eventually_LHE_pos (t z : ℝ) (ht0 : 0< t) (ht1 : t<1)
    (hz0 : 0< z) (hz1 : z<1) :
    ∀ᶠ m in atTop, 0< lowerEvent t ht0.le ht1.le m ∧
      0< boundaryEvent t m ∧ 0< duplicateEvent z hz0.le hz1.le m := by
  filter_upwards [eventually_count_geometry,capacity_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop (2:ℕ)] with m hm hc1 hm2
  have hL := LowBody.pmf_pos (m-1) (c m-1) ((1+t)/2)
    (by linarith) (by linarith) (by omega)
  have hLlo := LowBody.pmf_le_lower_tail (m-1) (c m-1) ((1+t)/2)
    (by linarith) (by linarith) (by omega)
  have hH1 := LowBody.pmf_pos (m-2) (otherLower m) t ht0 ht1
    (by dsimp [otherLower]; omega)
  have hH2 := LowBody.pmf_pos (2*c m) (c m-otherLower m-1) (1/2)
    (by norm_num) (by norm_num) (by omega)
  have hE := LowBody.pmf_pos (m-2) (m-2*c m) z hz0 hz1 (by omega)
  have hElo := pmf_le_upper_tail (m-2) (m-2*c m) z hz0.le hz1.le (by omega)
  exact ⟨hL.trans_le hLlo,mul_pos hH1 hH2,hE.trans_le hElo⟩

lemma tendsto_zero_of_positive_log_rate (F : ℕ→ℝ) (a : ℝ) (ha : 0< a)
    (hF : ∀ᶠ m in atTop,0< F m)
    (hlog : Tendsto (fun m => -log (F m)/(m:ℝ)) atTop (𝓝 a)) :
    Tendsto F atTop (𝓝 0) := by
  have hrate := hlog.eventually_const_lt (show a/2< a by linarith)
  have hexp : Tendsto (fun m : ℕ => exp (-(m:ℝ)*(a/2))) atTop (𝓝 0) := by
    have hmTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have htop := hmTop.const_mul_atTop (show 0< a/2 by linarith)
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp htop using 1
    funext m
    congr 1
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
  · exact hF.mono (fun _ h => h.le)
  · filter_upwards [hF,hrate,eventually_gt_atTop (0:ℕ)] with m hFp hm hm0
    have hmR : (0:ℝ)< m := Nat.cast_pos.mpr hm0
    have hnum := (lt_div_iff₀ hmR).mp hm
    have hl : log (F m)≤-(m:ℝ)*(a/2) := by linarith
    have he := Real.exp_le_exp.mpr hl
    rwa [Real.exp_log hFp] at he

theorem sourceCoefficient_log_rate (η χ t z : ℝ)
    (hη : 0<η) (hχ : χ<1) (ht0 : 0< t) (ht1 : t<1)
    (hz0 : 0< z) (hzδ : z<δ) :
    Tendsto (fun m => -log (sourceCoefficient η χ t z ht0.le ht1.le hz0.le
      (hzδ.trans (by norm_num [Uniform07.delta] : δ<1)).le m)/(m:ℝ))
      atTop (𝓝 (duplicateRate z-lowerRate t-boundaryRate t)) := by
  have hz1 : z<1 := hzδ.trans (by norm_num [Uniform07.delta])
  let C : ℝ := 4*η/(1-χ)
  have hC : 0< C := div_pos (by positivity) (sub_pos.mpr hχ)
  have hL := literal_L_log_rate t ht0 ht1
  have hH := literal_H_log_rate t ht0 ht1
  have hE := literal_E_log_rate z hz0 hzδ
  have hlogC := tendsto_const_div_atTop_nhds_zero_nat (log C)
  have hlogm : Tendsto (fun m : ℕ => log ((m-1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 0) := by
    have hh := log_card_div_tendsto_zero (fun m => m-2) 1
      (tendsto_sub_atTop_nat 2) (LowBody.tendsto_trials_fraction 2)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with m hm
    rw [show m-2+1=m-1 by omega]
  have hh := (((hE.sub hL).sub hH).sub hlogC).sub hlogm
  have hh' : Tendsto (fun m : ℕ =>
      -log (duplicateEvent z hz0.le hz1.le m)/(m:ℝ) -
      (-log (lowerEvent t ht0.le ht1.le m)/(m:ℝ)) -
      (-log (boundaryEvent t m)/(m:ℝ)) -
      log C/(m:ℝ) - log ((m-1:ℕ):ℝ)/(m:ℝ))
      atTop (𝓝 (duplicateRate z-lowerRate t-boundaryRate t)) := by
    simpa only [sub_zero] using hh
  apply hh'.congr'
  filter_upwards [eventually_LHE_pos t z ht0 ht1 hz0 hz1,
    eventually_gt_atTop (1:ℕ)] with m hm hm1
  have hmR : (0:ℝ)<((m-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hid : sourceCoefficient η χ t z ht0.le ht1.le hz0.le hz1.le m =
      C*((m-1:ℕ):ℝ)*duplicateEvent z hz0.le hz1.le m /
        (lowerEvent t ht0.le ht1.le m*boundaryEvent t m) := by
    dsimp [sourceCoefficient,C]
    field_simp [(sub_pos.mpr hχ).ne',hm.1.ne',hm.2.1.ne']
  rw [hid,Real.log_div (mul_ne_zero (mul_ne_zero hC.ne' hmR.ne') hm.2.2.ne')
    (mul_ne_zero hm.1.ne' hm.2.1.ne'),
    Real.log_mul (mul_ne_zero hC.ne' hmR.ne') hm.2.2.ne',
    Real.log_mul hC.ne' hmR.ne',Real.log_mul hm.1.ne' hm.2.1.ne']
  ring

theorem sourceCoefficient_tendsto_zero (η χ t z : ℝ)
    (hη : 0<η) (hχ : χ<1) (ht0 : 0< t) (ht1 : t<1)
    (hz0 : 0< z) (hzδ : z<δ)
    (hgap : lowerRate t+boundaryRate t< duplicateRate z) :
    Tendsto (sourceCoefficient η χ t z ht0.le ht1.le hz0.le
      (hzδ.trans (by norm_num [Uniform07.delta] : δ<1)).le) atTop (𝓝 0) := by
  have hz1 : z<1 := hzδ.trans (by norm_num [Uniform07.delta])
  apply tendsto_zero_of_positive_log_rate _
    (duplicateRate z-lowerRate t-boundaryRate t) (by linarith) _
    (sourceCoefficient_log_rate η χ t z hη hχ ht0 ht1 hz0 hzδ)
  filter_upwards [eventually_LHE_pos t z ht0 ht1 hz0 hz1,
    eventually_gt_atTop (1:ℕ)] with m hm hm1
  have hmR : (0:ℝ)<((m-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  dsimp [sourceCoefficient]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hη) hmR) hm.2.2)
    (mul_pos (mul_pos (sub_pos.mpr hχ) hm.1) hm.2.1)

theorem eventually_sourceCoefficient_lt_half (η χ t z : ℝ)
    (hη : 0<η) (hχ : χ<1) (ht0 : 0< t) (ht1 : t<1)
    (hz0 : 0< z) (hzδ : z<δ)
    (hgap : lowerRate t+boundaryRate t< duplicateRate z) :
    ∀ᶠ m in atTop,
      sourceCoefficient η χ t z ht0.le ht1.le hz0.le
        (hzδ.trans (by norm_num [Uniform07.delta] : δ<1)).le m < 1/2 :=
  (sourceCoefficient_tendsto_zero η χ t z hη hχ ht0 ht1 hz0 hzδ hgap).eventually_lt_const
    (by norm_num : (0:ℝ)<1/2)

theorem duplicate_over_lower_square_tendsto_zero (t z : ℝ)
    (ht0 : 0< t) (ht1 : t<1) (hz0 : 0< z) (hzδ : z<δ)
    (hgap : 2*lowerRate t< duplicateRate z) :
    Tendsto (fun m => duplicateEvent z hz0.le
      (hzδ.trans (by norm_num [Uniform07.delta] : δ<1)).le m /
        (lowerEvent t ht0.le ht1.le m)^2) atTop (𝓝 0) := by
  have hz1 : z<1 := hzδ.trans (by norm_num [Uniform07.delta])
  let F : ℕ→ℝ := fun m => duplicateEvent z hz0.le hz1.le m /
    (lowerEvent t ht0.le ht1.le m)^2
  have hF : ∀ᶠm in atTop,0< F m := by
    filter_upwards [eventually_LHE_pos t z ht0 ht1 hz0 hz1] with m hm
    exact div_pos hm.2.2 (pow_pos hm.1 2)
  have hlog : Tendsto (fun m => -log (F m)/(m:ℝ)) atTop
      (𝓝 (duplicateRate z-2*lowerRate t)) := by
    have hh := (literal_E_log_rate z hz0 hzδ).sub ((literal_L_log_rate t ht0 ht1).const_mul 2)
    apply hh.congr'
    filter_upwards [eventually_LHE_pos t z ht0 ht1 hz0 hz1] with m hm
    dsimp [F]
    rw [Real.log_div hm.2.2.ne' (pow_ne_zero _ hm.1.ne'),Real.log_pow]
    ring
  exact tendsto_zero_of_positive_log_rate F (duplicateRate z-2*lowerRate t)
    (by linarith) hF hlog

end FCAppendix.Affine.UniformFinite.AtomEvents
