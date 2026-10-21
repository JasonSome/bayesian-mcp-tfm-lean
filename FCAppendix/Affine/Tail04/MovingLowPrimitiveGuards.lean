import FCAppendix.Affine.LowBody.NoisyAtomlessLimit

noncomputable section
namespace FCAppendix.Affine.Tail04.MovingLow
open MeasureTheory ProbabilityTheory Set Filter Topology Real Classical
open LowBody
open scoped BigOperators

def categories (s a h : ℝ) (hs : 0 ≤ s) (_ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (hm : ℕ → ℝ) (hm0 : ∀ m, 0 ≤ hm m)
    (hma : ∀ m, hm m ≤ a) (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (m : ℕ) : FiniteLaw (Fin 4) :=
  categoryLaw s (a-hm m) (h+hm m) hs (sub_nonneg.mpr (hma m))
    (add_nonneg hh (hm0 m)) (by linarith) Gref

theorem eventually_joint_upper (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a)
    (hh : 0 ≤ h) (hsum : s+a+h=1)
    (hm : ℕ → ℝ) (hm0 : ∀ m, 0 ≤ hm m) (hma : ∀ m, hm m ≤ a)
    (hm_lim : Tendsto hm atTop (𝓝 0))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (rho : ℝ)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (k : ℕ) (t : ℝ) (ht : t ≤ 0) (v : ℝ)
    (hv : v < jointObjective s a h rho t) :
    ∀ᶠ m : ℕ in atTop,
      (CommonList.iid (categories s a h hs.le ha hh hsum hm hm0 hma Gref m) (m-k)).prob
        (BothUnderflow (c m)) ≤ exp (-(m:ℝ)*v) := by
  let Z : ℕ → ℝ := fun m => (a-hm m)*exp (2*t)+(h+hm m)*exp t+s
  let Z0 : ℝ := a*exp (2*t)+h*exp t+s
  have hZ0 : 0 < Z0 := by dsimp [Z0]; positivity
  have hZ : Tendsto Z atTop (𝓝 Z0) := by
    convert! (((tendsto_const_nhds.sub hm_lim).mul_const (exp (2*t))).add
      ((tendsto_const_nhds.add hm_lim).mul_const (exp t))).add_const s using 1 ;
      simp [Z0]
  have hlog : Tendsto (fun m => log (Z m)) atTop (𝓝 (log Z0)) :=
    (Real.continuousAt_log hZ0.ne').tendsto.comp hZ
  have hexponent : Tendsto (fun m : ℕ =>
      (-2*t)*((c m:ℝ)/(m:ℝ))+(((m-k:ℕ):ℝ)/(m:ℝ))*log (Z m))
      atTop (𝓝 (-jointObjective s a h rho t)) := by
    convert! (hc.const_mul (-2*t)).add ((tendsto_trials_fraction k).mul hlog) using 1 ;
      simp [jointObjective,Z0] ; ring
  have he := hexponent.eventually_lt_const
    (show -jointObjective s a h rho t < -v by linarith)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with m hem hmpos
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hmpos
  have hchern := bothUnderflow_chernoff s (a-hm m) (h+hm m) hs.le
    (sub_nonneg.mpr (hma m)) (add_nonneg hh (hm0 m)) (by linarith)
    Gref (m-k) (c m) t ht
  apply hchern.trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_lt_mul_of_pos_left hem hmR
  have heq : (m:ℝ)*((-2*t)*((c m:ℝ)/(m:ℝ))+
      (((m-k:ℕ):ℝ)/(m:ℝ))*log (Z m)) =
        -2*t*(c m:ℝ)+((m-k:ℕ):ℝ)*log (Z m) := by
    field_simp [hmR.ne']
  rw [heq] at hmul
  simpa only [Z,mul_neg,neg_mul] using hmul.le

theorem eventually_pmf_uniform (c : ℕ → ℕ) (rho q0 q1 : ℝ)
    (hrho : 0 < rho) (hq : rho < q0) (hqq : q0 ≤ q1) (hq1 : q1 < 1)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 rho)) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      c m-1 ≤ m-k ∧ ∀ q ∈ Icc q0 q1,
        PiBinomial.pmf (m-k) q1 (c m-1) ≤ PiBinomial.pmf (m-k) q (c m-1) := by
  have he := (tendsto_boundary_trials_fraction c rho hrho hc k).eventually_lt_const hq
  filter_upwards [he,eventually_gt_atTop k] with m hm hmk
  have hN : 0 < ((m-k:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hKN : c m-1 ≤ m-k := by
    have hh : ((c m-1:ℕ):ℝ)/((m-k:ℕ):ℝ) < 1 := hm.trans (hqq.trans_lt hq1)
    exact (Nat.cast_lt.mp ((div_lt_one hN).mp hh)).le
  have hmode : ((c m-1:ℕ):ℝ) ≤ ((m-k:ℕ):ℝ)*q0 := by
    have hh := (div_lt_iff₀ hN).mp hm
    simpa only [mul_comm q0] using hh.le
  refine ⟨hKN,?_⟩
  intro q hq'
  exact pmf_antitone_above_mode (m-k) (c m-1) hKN q0 q1
    (hrho.trans hq) hq1 hmode hq' ⟨hqq,le_rfl⟩ hq'.2

theorem eventually_lower_and_boundary (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a)
    (hh : 0 < h) (hsum : s+a+h=1)
    (hm : ℕ → ℝ) (hm0 : ∀ m, 0 ≤ hm m) (hma : ∀ m, hm m ≤ a)
    (hm_lim : Tendsto hm atTop (𝓝 0))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (rho : ℝ) (hrho : 0 < rho) (hrank : rho < a+h/2)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (r : ℝ) (hr : Ample.binaryKL rho (1-h/2) < r) :
    ∀ᶠ m : ℕ in atTop,
      0 < c m ∧
      exp (-(m:ℝ)*r) ≤
        (CommonList.iid (categories s a h hs.le ha hh.le hsum hm hm0 hma Gref m)
          (m-1)).prob (LocalUnderflow (c m) 0) ∧
      exp (-(m:ℝ)*r) ≤ boundary c (1-h/2) m ∧
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (u : ℝ),
        boundary c (1-h/2) m ≤
          PiBinomial.pmf (m-2) (higherBidProbability s (a-hm m) (h+hm m) G u) (c m-1) := by
  let q0 := (rho+(a+h/2))/2
  let p := 1-h/2
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hrho1 : rho < 1 := by linarith
  have hq : rho < q0 := by dsimp [q0]; linarith
  have hqtop : q0 < a+h/2 := by dsimp [q0]; linarith
  have hqq : q0 ≤ p := by dsimp [q0,p]; linarith
  have hlowlim : Tendsto (fun m => a+h/2-hm m/2) atTop (𝓝 (a+h/2)) := by
    simpa using tendsto_const_nhds.sub (hm_lim.div_const 2)
  have hsmall := hlowlim.eventually_const_lt hqtop
  have hfirst := eventually_pmf_exponential_lower (fun m => m-1) (fun m => c m-1)
    p rho hp0 hp1 hrho hrho1 (tendsto_sub_atTop_nat 1) (tendsto_trials_fraction 1)
    (tendsto_boundary_trials_fraction c rho hrho hc 1) r hr
  have hsecond := eventually_pmf_exponential_lower (fun m => m-2) (fun m => c m-1)
    p rho hp0 hp1 hrho hrho1 (tendsto_sub_atTop_nat 2) (tendsto_trials_fraction 2)
    (tendsto_boundary_trials_fraction c rho hrho hc 2) r hr
  have hmode1 := eventually_pmf_uniform c rho q0 p hrho hq hqq hp1 hc 1
  have hmode2 := eventually_pmf_uniform c rho q0 p hrho hq hqq hp1 hc 2
  have hcap : ∀ᶠ m : ℕ in atTop, 0 < c m := by
    filter_upwards [hc.eventually_const_lt hrho,eventually_gt_atTop (0:ℕ)] with m hcm hmpos
    have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hmpos
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hmR).mp hcm)
  filter_upwards [hsmall,hfirst,hsecond,hmode1,hmode2,hcap] with m hsm h1 h2 hB1 hB2 hcm
  have hmnonneg := hm0 m
  have hsumM : s+(a-hm m)+(h+hm m)=1 := by linarith
  have hpM : 1-(h+hm m)/2 ∈ Icc q0 p := by
    constructor <;> dsimp [p] at * <;> linarith
  have hpM0 : 0 ≤ 1-(h+hm m)/2 := (hrho.trans hq).le.trans hpM.1
  have hpM1 : 1-(h+hm m)/2 ≤ 1 := hpM.2.trans hp1.le
  refine ⟨hcm,?_,h2,?_⟩
  · rw [categories,localUnderflow_probability s (a-hm m) (h+hm m)
      hs.le (sub_nonneg.mpr (hma m)) (add_nonneg hh.le hmnonneg) hsumM Gref
      (m-1) (c m) hcm]
    exact h1.trans ((hB1.2 _ hpM).trans
      (pmf_le_lower_tail (m-1) (c m-1) (1-(h+hm m)/2) hpM0 hpM1 hB1.1))
  · intro G hG u
    letI := hG
    have hb := higherBidProbability_bounds s (a-hm m) (h+hm m) hs.le hsumM G u
    have hb' : higherBidProbability s (a-hm m) (h+hm m) G u ∈ Icc q0 p := by
      constructor <;> dsimp [p] at * <;> linarith [hb.1,hb.2]
    exact hB2.2 _ hb'

theorem eventually_primitive_guards (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a)
    (hh : 0 < h) (hsum : s+a+h=1)
    (hm : ℕ → ℝ) (hm0 : ∀ m, 0 ≤ hm m) (hma : ∀ m, hm m ≤ a)
    (hm_lim : Tendsto hm atTop (𝓝 0))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (rho eta : ℝ) (hrho : 0 < rho) (hrank : rho < a+h/2)
    (heta : 0 ≤ eta)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (hgap : 2*Ample.binaryKL rho (1-h/2) < jointRate s a h rho) :
    ∀ᶠ m : ℕ in atTop,
      let Cm := categories s a h hs.le ha hh.le hsum hm hm0 hma Gref m
      let L := (CommonList.iid Cm (m-1)).prob (LocalUnderflow (c m) 0)
      let H := boundary c (1-h/2) m
      let D := (CommonList.iid Cm (m-1)).prob (BothUnderflow (c m))
      let E := (CommonList.iid Cm (m-2)).prob (BothUnderflow (c m))
      2 < m ∧ 0 < c m ∧ 0 < L ∧ E < H ∧ D ≤ L/4 ∧
        8*eta*((m-1:ℕ):ℝ)*E/(L*(H-E)) < 1/2 ∧
        ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (u : ℝ),
          H ≤ PiBinomial.pmf (m-2)
            (higherBidProbability s (a-hm m) (h+hm m) G u) (c m-1) := by
  let I := Ample.binaryKL rho (1-h/2)
  have hp0 : 0 < 1-h/2 := by linarith
  have hp1 : 1-h/2 < 1 := by linarith
  have hrho1 : rho < 1 := by linarith
  have hI : 0 ≤ I := binaryKL_nonneg hp0 hp1 hrho hrho1
  obtain ⟨t,ht,hb⟩ := exists_negative_joint_tilt s a h rho I hgap
  let b := jointObjective s a h rho t
  let delta := (b-2*I)/8
  let r := I+delta
  let v := b-delta
  have hd : 0 < delta := by dsimp [delta,b]; linarith
  have hrI : I < r := by dsimp [r]; linarith
  have hr : 0 < r := hI.trans_lt hrI
  have hv : v < jointObjective s a h rho t := by dsimp [v,b]; linarith
  have hvr : 2*r < v := by dsimp [r,v,delta]; linarith
  let Cm := categories s a h hs.le ha hh.le hsum hm hm0 hma Gref
  let L := fun m : ℕ => (CommonList.iid (Cm m) (m-1)).prob (LocalUnderflow (c m) 0)
  let H := boundary c (1-h/2)
  let D := fun m : ℕ => (CommonList.iid (Cm m) (m-1)).prob (BothUnderflow (c m))
  let E := fun m : ℕ => (CommonList.iid (Cm m) (m-2)).prob (BothUnderflow (c m))
  have hl := eventually_lower_and_boundary s a h hs ha hh hsum hm hm0 hma hm_lim
    Gref c rho hrho hrank hc r hrI
  have hd1 := eventually_joint_upper s a h hs ha hh.le hsum hm hm0 hma hm_lim
    Gref c rho hc 1 t ht.le v hv
  have hd2 := eventually_joint_upper s a h hs ha hh.le hsum hm hm0 hma hm_lim
    Gref c rho hc 2 t ht.le v hv
  have hlo : ∀ᶠ m : ℕ in atTop, exp (-(m:ℝ)*r) ≤ L m ∧ exp (-(m:ℝ)*r) ≤ H m :=
    hl.mono (fun _ hm => ⟨hm.2.1,hm.2.2.1⟩)
  have hu : ∀ᶠ m : ℕ in atTop, D m ≤ exp (-(m:ℝ)*v) ∧ E m ≤ exp (-(m:ℝ)*v) :=
    hd1.and hd2
  have hg := eventually_guards_of_exponential_bounds L H D E eta r v heta hr hvr
    (fun m => (CommonList.iid (Cm m) (m-2)).prob_nonneg _) hlo hu
  filter_upwards [hg,hl,eventually_gt_atTop (2:ℕ)] with m hguards hlower hm2
  exact ⟨hm2,hlower.1,hguards.1,hguards.2.1,hguards.2.2.1,
    hguards.2.2.2,hlower.2.2.2⟩

theorem eventually_exists_actual_atomless_low_limit {d xi : ℝ}
    (hd : 0 ≤ d) (hxi : 0 < xi) (hxih : xi ≤ 1/2)
    (s a h : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s+a+h=1)
    (hm : ℕ → ℝ) (hm0 : ∀ m, 0 ≤ hm m) (hma : ∀ m, hm m ≤ a)
    (hm_lim : Tendsto hm atTop (𝓝 0))
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ → ℕ) (rho : ℝ) (hrho : 0 < rho) (hrank : rho < a+h/2)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 rho))
    (hgap : 2*Ample.binaryKL rho (1-h/2) < jointRate s a h rho)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐ w ∂mu, 0 < w.1) :
    ∀ᶠ m : ℕ in atTop, Nonempty
      (ActualAtomlessLowLimit (m-1) d xi (c m)
        (categories s a h hs.le ha hh.le hsum hm hm0 hma Gref m) mu) := by
  have hg := eventually_primitive_guards s a h hs ha hh hsum hm hm0 hma hm_lim Gref
    c rho (1-2*xi) hrho hrank (by linarith) hc hgap
  filter_upwards [hg] with m hmguard
  obtain ⟨hm2,hcm,hL,hE,hD,hcoef,huniform⟩ := hmguard
  have hmN : m-2+1=m-1 := by omega
  simp only [categories] at hL hE hD hcoef huniform ⊢
  have hf := LowBody.exists_actual_atomless_low_limit (N:=m-2) hd hxi hxih (c m) hcm
    s (a-hm m) (h+hm m) hs (sub_nonneg.mpr (hma m)) (add_nonneg hh.le (hm0 m))
    (by linarith) Gref hL (by rw [hmN]) (by rw [hmN]; exact hD)
    hE huniform (by rw [hmN]; exact hcoef) mu hmu
  simpa only [hmN] using hf

end FCAppendix.Affine.Tail04.MovingLow
