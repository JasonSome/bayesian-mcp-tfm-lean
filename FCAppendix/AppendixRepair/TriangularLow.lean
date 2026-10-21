import FCAppendix.Affine.LowBody.ActualLowBidEquilibrium

noncomputable section
namespace FCAppendix.Affine.AppendixRepair.TriangularLow
open MeasureTheory ProbabilityTheory Set Filter Topology Real Classical
open LowBody
open Existence.Distributional
open scoped BigOperators

structure CategoryRows where
  s : ℕ → ℝ
  a : ℕ → ℝ
  h : ℕ → ℝ
  s_nonneg : ∀ m, 0 ≤ s m
  a_nonneg : ∀ m, 0 ≤ a m
  h_nonneg : ∀ m, 0 ≤ h m
  total : ∀ m, s m + a m + h m = 1

def CategoryRows.law (C : CategoryRows) (G : Measure ℝ) [IsProbabilityMeasure G]
    (m : ℕ) : FiniteLaw (Fin 4) :=
  categoryLaw (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G

def CategoryRows.oneUnderflow (C : CategoryRows) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ → ℕ) (m : ℕ) : ℝ :=
  (CommonList.iid (C.law G m) (m - 1)).prob (LocalUnderflow (c m) 0)

def CategoryRows.jointUnderflow (C : CategoryRows) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ → ℕ) (k m : ℕ) : ℝ :=
  (CommonList.iid (C.law G m) (m - k)).prob (BothUnderflow (c m))

def CategoryRows.boundary (C : CategoryRows) (c : ℕ → ℕ) (m : ℕ) : ℝ :=
  PiBinomial.pmf (m - 2) (1 - C.h m / 2) (c m - 1)

lemma CategoryRows.arrival_bounds (C : CategoryRows) (m : ℕ) :
    0 ≤ 1 - C.h m / 2 ∧ 1 - C.h m / 2 ≤ 1 := by
  have hs := C.s_nonneg m
  have ha := C.a_nonneg m
  have hh := C.h_nonneg m
  have ht := C.total m
  constructor <;> linarith

lemma CategoryRows.limit_simplex (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) :
    0 ≤ s ∧ 0 ≤ a ∧ 0 ≤ h ∧ s + a + h = 1 := by
  refine ⟨ge_of_tendsto hs (Eventually.of_forall C.s_nonneg),
    ge_of_tendsto ha (Eventually.of_forall C.a_nonneg),
    ge_of_tendsto hh (Eventually.of_forall C.h_nonneg), ?_⟩
  exact tendsto_nhds_unique ((hs.add ha).add hh)
    (by simp_rw [C.total]; exact tendsto_const_nhds)

theorem tendsto_binaryKL {q p : ℕ → ℝ} {q₀ p₀ : ℝ}
    (hq : Tendsto q atTop (𝓝 q₀)) (hp : Tendsto p atTop (𝓝 p₀))
    (hq0 : 0 < q₀) (hq1 : q₀ < 1) (hp0 : 0 < p₀) (hp1 : p₀ < 1) :
    Tendsto (fun m => Ample.binaryKL (q m) (p m)) atTop (𝓝 (Ample.binaryKL q₀ p₀)) := by
  have hfirst := (hq.div hp hp0.ne').log (div_pos hq0 hp0).ne'
  have hqbar := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  have hpbar := (tendsto_const_nhds (x := (1 : ℝ))).sub hp
  have hsecond := (hqbar.div hpbar (sub_pos.mpr hp1).ne').log
    (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hp1)).ne'
  exact (hq.mul hfirst).add (hqbar.mul hsecond)

theorem eventually_pmf_exponential_lower
    (N K : ℕ → ℕ) (p : ℕ → ℝ) (p₀ ρ : ℝ)
    (hp : Tendsto p atTop (𝓝 p₀)) (hp0 : 0 < p₀) (hp1 : p₀ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hN : Tendsto N atTop atTop)
    (hNm : Tendsto (fun m => (N m : ℝ) / (m : ℝ)) atTop (𝓝 1))
    (hKN : Tendsto (fun m => (K m : ℝ) / (N m : ℝ)) atTop (𝓝 ρ))
    (r : ℝ) (hr : Ample.binaryKL ρ p₀ < r) :
    ∀ᶠ m : ℕ in atTop, exp (-(m : ℝ) * r) ≤ PiBinomial.pmf (N m) (p m) (K m) := by
  have hN0 : ∀ᶠ m in atTop, 0 < N m := hN.eventually_gt_atTop 0
  have hK0 := hKN.eventually_const_lt hρ0
  have hK1 := hKN.eventually_lt_const hρ1
  have hpM0 := hp.eventually_const_lt hp0
  have hpM1 := hp.eventually_lt_const hp1
  have hlog : Tendsto (fun m => log ((N m + 1 : ℕ) : ℝ) / (N m : ℝ)) atTop (𝓝 0) := by
    have hadd : Tendsto (fun m : ℕ => (N m : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hN).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))
    have he := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hadd
    convert he using 1
    simp [Function.comp_def]
  have hlogm : Tendsto (fun m => log ((N m + 1 : ℕ) : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
    have he := hlog.mul hNm
    have hfun : (fun m => log ((N m + 1 : ℕ) : ℝ) / (N m : ℝ) *
        ((N m : ℝ) / (m : ℝ))) =ᶠ[atTop]
        (fun m => log ((N m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
      filter_upwards [hN0] with m hm
      have hmR : (N m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
      field_simp
    simpa only [zero_mul] using he.congr' hfun
  have hKL := tendsto_binaryKL hKN hp hρ0 hρ1 hp0 hp1
  have hbound := (hlogm.add (hNm.mul hKL)).eventually_lt_const (by simpa using hr)
  filter_upwards [hN0, hK0, hK1, hpM0, hpM1, hbound, eventually_gt_atTop (0 : ℕ)]
    with m hNpos hKpos hKsmall hpPos hpSmall hb hm
  have hNR : (0 : ℝ) < N m := Nat.cast_pos.mpr hNpos
  have hKR : (0 : ℝ) < K m := (div_pos_iff_of_pos_right hNR).mp hKpos
  have hKnat : 0 < K m := Nat.cast_pos.mp hKR
  have hKlt : K m < N m := Nat.cast_lt.mp ((div_lt_one hNR).mp hKsmall)
  have hpmf := pmf_pos (N m) (K m) (p m) hpPos hpSmall hKlt.le
  have hlo := log_pmf_entropy_lower (N m) (K m) (p m) hKnat hKlt hpPos hpSmall
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbb : log ((N m + 1 : ℕ) : ℝ) + (N m : ℝ) *
      Ample.binaryKL ((K m : ℝ) / N m) (p m) < (m : ℝ) * r := by
    have hbid : log ((N m + 1 : ℕ) : ℝ) / (m : ℝ) + (N m : ℝ) / (m : ℝ) *
        Ample.binaryKL ((K m : ℝ) / N m) (p m) =
        (log ((N m + 1 : ℕ) : ℝ) + (N m : ℝ) *
          Ample.binaryKL ((K m : ℝ) / N m) (p m)) / (m : ℝ) := by ring
    rw [hbid] at hb
    simpa only [mul_comm r] using (div_lt_iff₀ hmR).mp hb
  apply (Real.le_log_iff_exp_le hpmf).mp
  linarith

theorem eventually_binomial_lower (C : CategoryRows)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c : ℕ → ℕ) (h ρ : ℝ)
    (hh : Tendsto C.h atTop (𝓝 h)) (hp0 : 0 < 1 - h / 2)
    (hp1 : 1 - h / 2 < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (r : ℝ) (hr : Ample.binaryKL ρ (1 - h / 2) < r) :
    ∀ᶠ m : ℕ in atTop, exp (-(m : ℝ) * r) ≤ C.oneUnderflow G c m ∧
      exp (-(m : ℝ) * r) ≤ C.boundary c m := by
  have hp : Tendsto (fun m => 1 - C.h m / 2) atTop (𝓝 (1 - h / 2)) :=
    tendsto_const_nhds.sub (hh.div_const 2)
  have h1 := eventually_pmf_exponential_lower (fun m => m - 1) (fun m => c m - 1)
    (fun m => 1 - C.h m / 2) (1 - h / 2) ρ hp hp0 hp1 hρ0 hρ1
    (tendsto_sub_atTop_nat 1) (tendsto_trials_fraction 1)
    (tendsto_boundary_trials_fraction c ρ hρ0 hc 1) r hr
  have h2 := eventually_pmf_exponential_lower (fun m => m - 2) (fun m => c m - 1)
    (fun m => 1 - C.h m / 2) (1 - h / 2) ρ hp hp0 hp1 hρ0 hρ1
    (tendsto_sub_atTop_nat 2) (tendsto_trials_fraction 2)
    (tendsto_boundary_trials_fraction c ρ hρ0 hc 2) r hr
  have hK : ∀ᶠ m : ℕ in atTop, c m - 1 ≤ m - 1 := by
    have he := (tendsto_boundary_trials_fraction c ρ hρ0 hc 1).eventually_lt_const hρ1
    filter_upwards [he, eventually_gt_atTop (1 : ℕ)] with m hm hm1
    have hN : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    exact (Nat.cast_lt.mp ((div_lt_one hN).mp hm)).le
  have hcap : ∀ᶠ m : ℕ in atTop, 0 < c m := by
    filter_upwards [hc.eventually_const_lt hρ0, eventually_gt_atTop (0 : ℕ)] with m hm hm0
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hmR).mp hm)
  filter_upwards [h1, h2, hK, hcap] with m hm1 hm2 hKm hcm
  refine ⟨?_, hm2⟩
  have hb := pmf_le_lower_tail (m - 1) (c m - 1) (1 - C.h m / 2)
    (C.arrival_bounds m).1 (C.arrival_bounds m).2 hKm
  have he := localUnderflow_probability (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G (m - 1) (c m) hcm
  change exp (-(m : ℝ) * r) ≤
    (CommonList.iid (C.law G m) (m - 1)).prob (LocalUnderflow (c m) 0)
  rw [show C.law G m = categoryLaw (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G from rfl, he]
  exact hm1.trans hb

theorem eventually_joint_upper (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) (hs0 : 0 < s)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c : ℕ → ℕ) (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (k : ℕ) (t : ℝ) (ht : t ≤ 0) (v : ℝ)
    (hv : v < jointObjective s a h ρ t) :
    ∀ᶠ m : ℕ in atTop, C.jointUnderflow G c k m ≤ exp (-(m : ℝ) * v) := by
  let Z : ℕ → ℝ := fun m => C.a m * exp (2 * t) + C.h m * exp t + C.s m
  let Z₀ : ℝ := a * exp (2 * t) + h * exp t + s
  have hsimplex := C.limit_simplex hs ha hh
  have hZ₀ : 0 < Z₀ := by
    have h₁ := mul_nonneg hsimplex.2.1 (exp_pos (2 * t)).le
    have h₂ := mul_nonneg hsimplex.2.2.1 (exp_pos t).le
    dsimp [Z₀]
    linarith
  have hZ : Tendsto Z atTop (𝓝 Z₀) :=
    ((ha.mul_const (exp (2 * t))).add (hh.mul_const (exp t))).add hs
  have hlogZ := hZ.log hZ₀.ne'
  have hl : Tendsto (fun m : ℕ => (-2 * t) * ((c m : ℝ) / (m : ℝ)) +
      (((m - k : ℕ) : ℝ) / (m : ℝ)) * log (Z m)) atTop
      (𝓝 (-jointObjective s a h ρ t)) := by
    convert (hc.const_mul (-2 * t)).add ((tendsto_trials_fraction k).mul hlogZ) using 1
    dsimp [jointObjective, Z₀]
    ring
  have he := hl.eventually_lt_const (show -jointObjective s a h ρ t < -v by linarith)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with m hem hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hchern := bothUnderflow_chernoff (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G (m - k) (c m) t ht
  apply hchern.trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_lt_mul_of_pos_left hem hmR
  have hid : (m : ℝ) * ((-2 * t) * ((c m : ℝ) / (m : ℝ)) +
      (((m - k : ℕ) : ℝ) / (m : ℝ)) * log (Z m)) =
      -2 * t * c m + ((m - k : ℕ) : ℝ) * log (Z m) := by field_simp
  rw [hid] at hmul
  simpa only [mul_neg, neg_mul] using hmul.le

theorem eventually_boundary_uniform (C : CategoryRows) {a h : ℝ}
    (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (hh0 : 0 < h) (c : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ)) :
    ∀ᶠ m : ℕ in atTop, ∀ q ∈ Icc (C.a m + C.h m / 2) (1 - C.h m / 2),
      C.boundary c m ≤ PiBinomial.pmf (m - 2) q (c m - 1) := by
  have hlo : Tendsto (fun m => C.a m + C.h m / 2) atTop (𝓝 (a + h / 2)) :=
    ha.add (hh.div_const 2)
  have hfrac := tendsto_boundary_trials_fraction c ρ hρ hc 2
  have hdiff := (hlo.sub hfrac).eventually_const_lt (sub_pos.mpr hrank)
  have hlo0 := hlo.eventually_const_lt (hρ.trans hrank)
  have hhpos := hh.eventually_const_lt hh0
  filter_upwards [hdiff, hlo0, hhpos, eventually_gt_atTop (2 : ℕ)]
    with m hd hq0 hhm hm2
  have hq1 : 1 - C.h m / 2 < 1 := by linarith
  have hqq : C.a m + C.h m / 2 ≤ 1 - C.h m / 2 := by
    linarith [C.total m, C.s_nonneg m]
  have hfr : ((c m - 1 : ℕ) : ℝ) / ((m - 2 : ℕ) : ℝ) < C.a m + C.h m / 2 := by
    linarith
  have hN : (0 : ℝ) < ((m - 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hKN : c m - 1 ≤ m - 2 := by
    have hf1 := hfr.trans (hqq.trans_lt hq1)
    exact (Nat.cast_lt.mp ((div_lt_one hN).mp hf1)).le
  have hmode : ((c m - 1 : ℕ) : ℝ) ≤ ((m - 2 : ℕ) : ℝ) * (C.a m + C.h m / 2) := by
    have hm := (div_lt_iff₀ hN).mp hfr
    simpa only [mul_comm (C.a m + C.h m / 2)] using hm.le
  intro q hq
  exact pmf_antitone_above_mode (m - 2) (c m - 1) hKN
    (C.a m + C.h m / 2) (1 - C.h m / 2) hq0 hq1 hmode
    hq ⟨hqq, le_rfl⟩ hq.2

theorem eventually_primitive_source_guards (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) (hs0 : 0 < s) (hh0 : 0 < h)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (c : ℕ → ℕ) (ρ η : ℝ)
    (hρ : 0 < ρ) (hrank : ρ < a + h / 2) (hη : 0 ≤ η)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ) :
    ∀ᶠ m : ℕ in atTop,
      0 < C.s m ∧ 2 < m ∧ 0 < c m ∧
      0 < C.oneUnderflow Gref c m ∧ C.jointUnderflow Gref c 2 m < C.boundary c m ∧
      C.jointUnderflow Gref c 1 m ≤ C.oneUnderflow Gref c m / 4 ∧
      8 * η * ((m - 1 : ℕ) : ℝ) * C.jointUnderflow Gref c 2 m /
        (C.oneUnderflow Gref c m * (C.boundary c m - C.jointUnderflow Gref c 2 m)) < 1 / 2 ∧
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (u : ℝ),
        C.boundary c m ≤ PiBinomial.pmf (m - 2)
          (higherBidProbability (C.s m) (C.a m) (C.h m) G u) (c m - 1) ∧
        C.boundary c m - C.jointUnderflow Gref c 2 m ≤
          (Measure.pi (fun _ : Fin (m - 2) => rivalLaw (C.s m) (C.a m) (C.h m) G)).real
            (firstCopyBoundary (c m) u) := by
  have hsimplex := C.limit_simplex hs ha hh
  have hh1 : h ≤ 1 := by linarith [hsimplex.1, hsimplex.2.1, hsimplex.2.2.2]
  have hp0 : 0 < 1 - h / 2 := by linarith
  have hp1 : 1 - h / 2 < 1 := by linarith
  have hq : a + h / 2 ≤ 1 - h / 2 := by linarith [hsimplex.1, hsimplex.2.2.2]
  have hρ1 : ρ < 1 := (hrank.trans_le hq).trans hp1
  let I := Ample.binaryKL ρ (1 - h / 2)
  have hI : 0 ≤ I := binaryKL_nonneg hp0 hp1 hρ hρ1
  obtain ⟨t, ht, hb⟩ := exists_negative_joint_tilt s a h ρ I hgap
  let b := jointObjective s a h ρ t
  let δ := (b - 2 * I) / 8
  let r := I + δ
  let v := b - δ
  have hδ : 0 < δ := by dsimp [δ, b]; linarith
  have hrI : I < r := by dsimp [r]; linarith
  have hr : 0 < r := hI.trans_lt hrI
  have hv : v < b := by dsimp [v]; linarith
  have hvr : 2 * r < v := by dsimp [r, v, δ]; linarith
  have hlo := eventually_binomial_lower C Gref c h ρ hh hp0 hp1 hρ hρ1 hc r hrI
  have hd := eventually_joint_upper C hs ha hh hs0 Gref c ρ hc 1 t ht.le v hv
  have he := eventually_joint_upper C hs ha hh hs0 Gref c ρ hc 2 t ht.le v hv
  have hguards := eventually_guards_of_exponential_bounds
    (C.oneUnderflow Gref c) (C.boundary c)
    (C.jointUnderflow Gref c 1) (C.jointUnderflow Gref c 2) η r v hη hr hvr
    (fun m => (CommonList.iid (C.law Gref m) (m - 2)).prob_nonneg _) hlo (hd.and he)
  have hboundary := eventually_boundary_uniform C ha hh hh0 c ρ hρ hrank hc
  have hcap : ∀ᶠ m : ℕ in atTop, 0 < c m := by
    filter_upwards [hc.eventually_const_lt hρ, eventually_gt_atTop (0 : ℕ)] with m hm hm0
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hmR).mp hm)
  filter_upwards [hs.eventually_const_lt hs0, hguards, hboundary, hcap,
    eventually_gt_atTop (2 : ℕ)] with m hsm hmR hmB hcm hm2
  refine ⟨hsm, hm2, hcm, hmR.1, hmR.2.1, hmR.2.2.1, hmR.2.2.2, ?_⟩
  intro G hG u
  letI := hG
  have hp := hmB (higherBidProbability (C.s m) (C.a m) (C.h m) G u)
    (higherBidProbability_bounds (C.s m) (C.a m) (C.h m)
      (C.s_nonneg m) (C.total m) G u)
  refine ⟨hp, ?_⟩
  have hactual := firstCopyBoundary_probability_lower (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G (m - 2) (c m) u
  rw [categoryLaw_eq_low_law (C.s m) (C.a m) (C.h m)
    (C.s_nonneg m) (C.a_nonneg m) (C.h_nonneg m) (C.total m) G Gref] at hactual
  exact (sub_le_sub_right hp _).trans hactual

theorem eventually_exists_actual_low_bid_equilibrium
    {d ξ : ℝ} (hd : 0 ≤ d) (hξ : 0 < ξ) (hξh : ξ ≤ 1 / 2)
    (C : CategoryRows) {s a h : ℝ}
    (hs : Tendsto C.s atTop (𝓝 s)) (ha : Tendsto C.a atTop (𝓝 a))
    (hh : Tendsto C.h atTop (𝓝 h)) (hs0 : 0 < s) (hh0 : 0 < h)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (c : ℕ → ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∀ᶠ m : ℕ in atTop,
      ∃ L : ActualAtomlessLowLimit (m - 1) d ξ (c m) (C.law Gref m) mu,
        ∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ b : ℝ, 0 ≤ b →
          exactExpectedPayoff (m - 1) d ξ (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
          exactExpectedPayoff (m - 1) d ξ (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1) := by
  have hg := eventually_primitive_source_guards C hs ha hh hs0 hh0 Gref c ρ (1 - 2 * ξ)
    hρ hrank (by linarith) hc hgap
  filter_upwards [hg] with m hm
  obtain ⟨hsm, hm2, hcm, hL, hE, hD, hcoef, huniform⟩ := hm
  have hmN : m - 2 + 1 = m - 1 := by omega
  have hf := exists_actual_atomless_low_limit (N := m - 2) hd hξ hξh (c m) hcm
    (C.s m) (C.a m) (C.h m) hsm (C.a_nonneg m) (C.h_nonneg m) (C.total m) Gref
    hL (by rw [hmN]; rfl) (by rw [hmN]; exact hD) hE
    (fun G hG u => (huniform G hG u).1) (by rw [hmN]; exact hcoef) mu hmu
  have hf' : Nonempty (ActualAtomlessLowLimit (m - 1) d ξ (c m) (C.law Gref m) mu) := by
    simpa only [hmN, CategoryRows.law] using hf
  obtain ⟨L⟩ := hf'
  exact ⟨L, L.all_bid_IC hξ hξh⟩

def privatePartialRows (s a h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hsum : s + a + h = 1) (partialMass : ℕ → ℝ)
    (hpartial0 : ∀ m, 0 ≤ partialMass m) (hpartiala : ∀ m, partialMass m ≤ a) : CategoryRows where
  s := fun _ => s
  a := fun m => a - partialMass m
  h := fun m => h + partialMass m
  s_nonneg := fun _ => hs
  a_nonneg := fun m => sub_nonneg.mpr (hpartiala m)
  h_nonneg := fun m => add_nonneg hh (hpartial0 m)
  total := by intro m; linarith

theorem privatePartialRows_tendsto (s a h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hsum : s + a + h = 1) (partialMass : ℕ → ℝ)
    (hpartial0 : ∀ m, 0 ≤ partialMass m) (hpartiala : ∀ m, partialMass m ≤ a)
    (hpartial : Tendsto partialMass atTop (𝓝 0)) :
    let C := privatePartialRows s a h hs hh hsum partialMass hpartial0 hpartiala
    Tendsto C.s atTop (𝓝 s) ∧ Tendsto C.a atTop (𝓝 a) ∧ Tendsto C.h atTop (𝓝 h) := by
  refine ⟨tendsto_const_nhds, ?_, ?_⟩
  · convert! (tendsto_const_nhds (x := a)).sub hpartial using 1; simp only [sub_zero]
  · convert! (tendsto_const_nhds (x := h)).add hpartial using 1; simp only [add_zero]

theorem eventually_exists_partial_private_low_bid_equilibrium
    {d ξ : ℝ} (hd : 0 ≤ d) (hξ : 0 < ξ) (hξh : ξ ≤ 1 / 2)
    (s a h : ℝ) (hs : 0 < s) (hh : 0 < h) (hsum : s + a + h = 1)
    (partialMass : ℕ → ℝ) (hpartial0 : ∀ m, 0 ≤ partialMass m)
    (hpartiala : ∀ m, partialMass m ≤ a) (hpartial : Tendsto partialMass atTop (𝓝 0))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref] (c : ℕ → ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hrank : ρ < a + h / 2)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hgap : 2 * Ample.binaryKL ρ (1 - h / 2) < jointRate s a h ρ)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    let C := privatePartialRows s a h hs.le hh.le hsum partialMass hpartial0 hpartiala
    ∀ᶠ m : ℕ in atTop,
      ∃ L : ActualAtomlessLowLimit (m - 1) d ξ (c m) (C.law Gref m) mu,
        ∀ᵐ x ∂(L.joint.1 : Measure (LowValue d × LowValue d)), ∀ b : ℝ, 0 ≤ b →
          exactExpectedPayoff (m - 1) d ξ (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, b) ≤
          exactExpectedPayoff (m - 1) d ξ (c m) (C.law Gref m)
            (L.joint.1.map measurable_snd.aemeasurable) (x.1.1, x.2.1) := by
  let C := privatePartialRows s a h hs.le hh.le hsum partialMass hpartial0 hpartiala
  have hl := privatePartialRows_tendsto s a h hs.le hh.le hsum partialMass
    hpartial0 hpartiala hpartial
  exact eventually_exists_actual_low_bid_equilibrium hd hξ hξh C
    hl.1 hl.2.1 hl.2.2 hs hh Gref c ρ hρ hrank hc hgap mu hmu

def HigherUnderflow {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4) : Prop :=
  (∑ i, firstHigher (kind i)) < c ∨ (∑ i, secondHigher (kind i)) < c

theorem higherUnderflow_le (C : CategoryRows)
    (G : Measure ℝ) [IsProbabilityMeasure G] (m N c : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : (c : ℝ) ≤ (N : ℝ) * (C.a m + C.h m / 2 - δ)) :
    (CommonList.iid (C.law G m) N).prob (HigherUnderflow c) ≤
      2 * exp (-2 * (N : ℝ) * δ ^ 2) := by
  have hmean₁ : (C.law G m).expect (fun k => (firstHigher k : ℝ)) =
      C.a m + C.h m / 2 := by
    rw [CategoryRows.law, categoryLaw_expect]
    norm_num [firstHigher, Fin.ext_iff]
  have hmean₂ : (C.law G m).expect (fun k => (secondHigher k : ℝ)) =
      C.a m + C.h m / 2 := by
    rw [CategoryRows.law, categoryLaw_expect]
    norm_num [secondHigher, Fin.ext_iff]
  have hbounded₁ (k : Fin 4) : (firstHigher k : ℝ) ∈ Icc (0 : ℝ) 1 := by
    fin_cases k <;> norm_num [firstHigher, Fin.ext_iff]
  have hbounded₂ (k : Fin 4) : (secondHigher k : ℝ) ∈ Icc (0 : ℝ) 1 := by
    fin_cases k <;> norm_num [secondHigher, Fin.ext_iff]
  have hfirst : (CommonList.iid (C.law G m) N).prob
      (fun kind => (∑ i, firstHigher (kind i)) < c) ≤
        exp (-2 * (N : ℝ) * δ ^ 2) := by
    have hbound := FiniteCramer.iid_lower_hoeffding (C.law G m)
      (fun k => (firstHigher k : ℝ)) hbounded₁ N hδ
    rw [hmean₁] at hbound
    apply ((CommonList.iid (C.law G m) N).prob_mono ?_).trans hbound
    intro kind hk
    have hkR : (∑ i, (firstHigher (kind i) : ℝ)) ≤ (c : ℝ) := by
      exact_mod_cast hk.le
    exact hkR.trans hc
  have hsecond : (CommonList.iid (C.law G m) N).prob
      (fun kind => (∑ i, secondHigher (kind i)) < c) ≤
        exp (-2 * (N : ℝ) * δ ^ 2) := by
    have hbound := FiniteCramer.iid_lower_hoeffding (C.law G m)
      (fun k => (secondHigher k : ℝ)) hbounded₂ N hδ
    rw [hmean₂] at hbound
    apply ((CommonList.iid (C.law G m) N).prob_mono ?_).trans hbound
    intro kind hk
    have hkR : (∑ i, (secondHigher (kind i) : ℝ)) ≤ (c : ℝ) := by
      exact_mod_cast hk.le
    exact hkR.trans hc
  have hu := (CommonList.iid (C.law G m) N).prob_union_le
    (fun kind => (∑ i, firstHigher (kind i)) < c)
    (fun kind => (∑ i, secondHigher (kind i)) < c)
  change (CommonList.iid (C.law G m) N).prob (HigherUnderflow c) ≤ _ at hu
  linarith

theorem eventually_higherUnderflow_exponential (C : CategoryRows) {a h : ℝ}
    (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (c : ℕ → ℕ) (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) [IsProbabilityMeasure G],
        (CommonList.iid (C.law G m) (m - 1)).prob (HigherUnderflow (c m)) ≤
          2 * exp (-2 * ((m - 1 : ℕ) : ℝ) * δ ^ 2) := by
  let δ := (a + h / 2 - ρ) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hcn : Tendsto (fun m => (c m : ℝ) / ((m - 1 : ℕ) : ℝ))
      atTop (𝓝 ρ) := by
    have hratio := hc.div (tendsto_trials_fraction 1) one_ne_zero
    have hratio' : Tendsto (fun m => ((c m : ℝ) / (m : ℝ)) /
        (((m - 1 : ℕ) : ℝ) / (m : ℝ))) atTop (𝓝 ρ) := by
      change Tendsto (fun m => ((c m : ℝ) / (m : ℝ)) /
        (((m - 1 : ℕ) : ℝ) / (m : ℝ))) atTop (𝓝 (ρ / 1)) at hratio
      simpa only [div_one] using hratio
    apply hratio'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hmR : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
    field_simp
  have hmargin := ((ha.add (hh.div_const 2)).sub hcn).eventually_const_lt
    (show δ < a + h / 2 - ρ by dsimp only [δ]; linarith)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmargin, eventually_gt_atTop (1 : ℕ)] with m hm hm1
  intro G hG
  letI := hG
  have hN : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcap : (c m : ℝ) ≤ ((m - 1 : ℕ) : ℝ) *
      (C.a m + C.h m / 2 - δ) := by
    have hr : (c m : ℝ) / ((m - 1 : ℕ) : ℝ) < C.a m + C.h m / 2 - δ := by
      linarith
    have he := (div_lt_iff₀ hN).mp hr
    simpa only [mul_comm] using he.le
  exact higherUnderflow_le C G m (m - 1) (c m) hδ.le hcap

theorem higherUnderflow_tendsto_zero (C : CategoryRows) {a h : ℝ}
    (ha : Tendsto C.a atTop (𝓝 a)) (hh : Tendsto C.h atTop (𝓝 h))
    (G : Measure ℝ) [IsProbabilityMeasure G] (c : ℕ → ℕ) (ρ : ℝ)
    (hc : Tendsto (fun m => (c m : ℝ) / (m : ℝ)) atTop (𝓝 ρ))
    (hrank : ρ < a + h / 2) :
    Tendsto (fun m => (CommonList.iid (C.law G m) (m - 1)).prob
      (HigherUnderflow (c m))) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hb⟩ := eventually_higherUnderflow_exponential C ha hh c ρ hc hrank
  have hq : 0 < 2 * δ ^ 2 := by positivity
  have he : Tendsto (fun m : ℕ => exp (-2 * ((m - 1 : ℕ) : ℝ) * δ ^ 2))
      atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)).const_mul_atTop hq)
    convert! ht using 1
    funext m
    simp only [Function.comp_def]
    congr 1
    ring
  have he2 : Tendsto (fun m : ℕ => 2 * exp (-2 * ((m - 1 : ℕ) : ℝ) * δ ^ 2))
      atTop (𝓝 0) := by simpa only [mul_zero] using he.const_mul 2
  exact squeeze_zero'
    (Eventually.of_forall fun m => (CommonList.iid (C.law G m) (m - 1)).prob_nonneg _)
    (hb.mono fun _ hm => hm G) he2

end FCAppendix.Affine.AppendixRepair.TriangularLow
