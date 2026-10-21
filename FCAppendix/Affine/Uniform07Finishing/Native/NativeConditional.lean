import FCAppendix.Affine.Uniform07Finishing.Native.LowerVersion
import FCAppendix.Affine.Uniform07Finishing.Native.SourceProfile
import FCAppendix.Probability.FinitePushforward
import FCAppendix.Finite.BalancedOrder
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_outcome_of_physical_count_coupling
    (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Sample m n Seed → Ω) (hT : MeasurePreserving T (sampleLaw Γ) P)
    (K : Ω → Fin (n+1)) (hK : Measurable K)
    (hcount : focalCount Γ i a =ᵐ[sampleLaw Γ] K ∘ T) :
    (problem Γ i).outcome a = CountLaw.ofMeasure P K hK := by
  rw [problem_outcome]
  apply (CountLaw.ofMeasure_congr_ae (sampleLaw Γ) (focalCount Γ i a) (K ∘ T)
    (measurable_focalCount Γ i a) (hK.comp hT.measurable) hcount).trans
  apply FiniteLaw.ext_expect
  intro f
  simp only [CountLaw.expect_ofMeasure]
  have hm := integral_map (μ := sampleLaw Γ) (φ := T) hT.measurable.aemeasurable
    (((measurable_of_finite f).comp hK).aestronglyMeasurable)
  rw [hT.map_eq] at hm
  exact hm.symm

theorem two_count_mass_formulas (P : CountLaw 2) :
    P.mass 0 = 1-P.load+P.duplicates ∧
    P.mass 1 = P.load-2*P.duplicates ∧
    P.mass 2 = P.duplicates := by
  have hL : P.load = P.mass 1+2*P.mass 2 := by
    norm_num [CountLaw.load, FiniteLaw.expect, Fin.sum_univ_succ]; ring
  have hS : P.success = P.mass 1+P.mass 2 := by
    norm_num [CountLaw.success, FiniteLaw.expect, Fin.sum_univ_succ, successIndicator]
  have hT : P.mass 0+P.mass 1+P.mass 2 = 1 := by
    have hh := P.total
    norm_num [Fin.sum_univ_succ] at hh
    linarith
  have hD : P.duplicates = P.mass 2 := by
    rw [CountLaw.duplicates, hL, hS]
    ring
  exact ⟨by linarith, by linarith, hD.symm⟩

theorem two_count_mass_error (P Q : CountLaw 2) {ε : ℝ} (hε : 0 ≤ ε)
    (hL : |P.load-Q.load| ≤ ε) (hD : |P.duplicates-Q.duplicates| ≤ ε)
    (r : Fin 3) : |P.mass r-Q.mass r| ≤ 3*ε := by
  have hp := two_count_mass_formulas P
  have hq := two_count_mass_formulas Q
  have hl := abs_le.mp hL
  have hd := abs_le.mp hD
  fin_cases r
  · change |P.mass 0-Q.mass 0| ≤ 3*ε
    rw [hp.1, hq.1]
    apply abs_le.mpr
    constructor <;> linarith
  · change |P.mass 1-Q.mass 1| ≤ 3*ε
    rw [hp.2.1, hq.2.1]
    apply abs_le.mpr
    constructor <;> linarith
  · change |P.mass 2-Q.mass 2| ≤ 3*ε
    rw [hp.2.2, hq.2.2]
    exact hD.trans (by linarith)

theorem probability_integral_error_of_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable f P) (q ε : ℝ)
    (herr : ∀ᵐ x ∂P, |f x-q| ≤ ε) : |(∫ x, f x ∂P)-q| ≤ ε := by
  have hlo := integral_mono_ae (integrable_const (q-ε)) hf
    (herr.mono fun x hx => by have := (abs_le.mp hx).1; linarith)
  have hhi := integral_mono_ae hf (integrable_const (q+ε))
    (herr.mono fun x hx => by have := (abs_le.mp hx).2; linarith)
  simp only [integral_const, probReal_univ, one_smul] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actual_conditional_mass_error (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (v : ℝ) (Q : CountLaw n) (ε : ℝ)
    (herr : ∀ i : Fin m, ∀ᵐ a ∂Γ.σ v, ∀ r : Fin (n+1),
      |((problem Γ i).outcome a).mass r-Q.mass r| ≤ ε) (r : Fin (n+1)) :
    |(conditionalTypeCountLaw Γ hm v).mass r-Q.mass r| ≤ ε := by
  have hi (i : Fin m) : |(typeOutcome Γ i v).mass r-Q.mass r| ≤ ε := by
    exact probability_integral_error_of_ae_bound (Γ.σ v)
      (FiniteLaw.integrable_mass (Γ.σ v) (problem Γ i).outcome
        (measurable_outcome_mass Γ i) r) _ _ ((herr i).mono fun a ha => ha r)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlo : Q.mass r-ε ≤ (∑ i, (typeOutcome Γ i v).mass r)/(m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show Q.mass r-ε ≤ (typeOutcome Γ i v).mass r by
        have := (abs_le.mp (hi i)).1
        linarith)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm] using hh
  have hhi : (∑ i, (typeOutcome Γ i v).mass r)/(m : ℝ) ≤ Q.mass r+ε := by
    apply (div_le_iff₀ hmR).mpr
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (typeOutcome Γ i v).mass r ≤ Q.mass r+ε by
        have := (abs_le.mp (hi i)).2
        linarith)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm] using hh
  change |(∑ i, (typeOutcome Γ i v).mass r)/(m : ℝ)-Q.mass r| ≤ ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actual_conditional_mass_tendsto_of_error
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) n (C k) Seed)
    (hM : ∀ k, 0 < M k) (v : ℝ) (Q : CountLaw n)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, ∀ i : Fin (M k), ∀ᵐ a ∂(Γ k).σ v,
      ∀ r : Fin (n+1), |((problem (Γ k) i).outcome a).mass r-Q.mass r| ≤ ε k)
    (r : Fin (n+1)) :
    Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hM k) v).mass r)
      atTop (𝓝 (Q.mass r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) _ hε
  exact herr.mono fun k hk => actual_conditional_mass_error (Γ k) (hM k) v Q (ε k) hk r

def lowerTargetProbability (lam v : ℝ) : ℝ := max (1-lam/v) 0
def lowerProductQuadratic (lam v p : ℝ) : ℝ := 2*(v-lam)*p-v*p^2

theorem lowerTargetProbability_mem {lam v : ℝ} (hlam : 0 ≤ lam) (hv : 0 < v) :
    lowerTargetProbability lam v ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_right _ _, max_le (by linarith [div_nonneg hlam hv.le]) (by norm_num)⟩

theorem lower_product_quadratic_gap {lam v p : ℝ} (hv : 0 < v) (hp : 0 ≤ p) :
    v*(p-lowerTargetProbability lam v)^2 ≤
      lowerProductQuadratic lam v (lowerTargetProbability lam v)-
        lowerProductQuadratic lam v p := by
  by_cases hvl : lam ≤ v
  · have hstar : 0 ≤ 1-lam/v := by
      have hd : lam/v ≤ 1 := (div_le_one hv).mpr hvl
      linarith
    have he : lowerProductQuadratic lam v (lowerTargetProbability lam v)-
        lowerProductQuadratic lam v p = v*(p-lowerTargetProbability lam v)^2 := by
      simp only [lowerTargetProbability, max_eq_left hstar, lowerProductQuadratic]
      field_simp [hv.ne']
      ring
    exact he.ge
  · have hstar : 1-lam/v ≤ 0 := by
      have hd : 1 ≤ lam/v := (one_le_div hv).mpr (le_of_not_ge hvl)
      linarith
    simp only [lowerTargetProbability, max_eq_right hstar, lowerProductQuadratic,
      mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_sub]
    have hn : (v-lam)*p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hp
    nlinarith

theorem actual_best_response_probability_error
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (v lam p ε : ℝ)
    (hv : 0 < v) (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (a a₀ : JointAction 2)
    (hbr : ∀ a' : JointAction 2, (problem Γ i).payoff v a' ≤ (problem Γ i).payoff v a)
    (hmenu : |(problem Γ i).payoff v a-lowerProductQuadratic lam v p| ≤ ε)
    (htest : lowerProductQuadratic lam v (lowerTargetProbability lam v)-ε ≤
      (problem Γ i).payoff v a₀) :
    |p-lowerTargetProbability lam v| ≤ Real.sqrt (2*ε/v) := by
  have hgap := lower_product_quadratic_gap (lam := lam) hv hp
  have hupper := (abs_le.mp hmenu).2
  have hbest := hbr a₀
  have hsq : (p-lowerTargetProbability lam v)^2 ≤ 2*ε/v := by
    apply (le_div_iff₀ hv).mpr
    nlinarith
  apply (Real.le_sqrt (abs_nonneg _) (div_nonneg (by positivity) hv.le)).mpr
  simpa only [sq_abs] using hsq

def sourceProductProbability (i : Uniform07.Row) (b : ℝ) : ℝ :=
  if b ≤ Uniform07.entry i then 0
  else (1-Uniform07.entry i/b)/Uniform07.xi i

theorem source_kappa_add_xi (i : Uniform07.Row) :
    Uniform07.kappa i+Uniform07.xi i = 1 := by
  cases i <;> norm_num [Uniform07.kappa, Uniform07.kappaQ, Uniform07.xi,
    Uniform07.xiQ, Uniform07.etaQ]

theorem source_kappa_pos (i : Uniform07.Row) : 0 < Uniform07.kappa i := by
  cases i <;> norm_num [Uniform07.kappa, Uniform07.kappaQ, Uniform07.xiQ,
    Uniform07.etaQ]

theorem sourceProduct_eta_le_one (i : Uniform07.Row) : Uniform07.eta i ≤ 1 := by
  cases i <;> norm_num [Uniform07.eta, Uniform07.etaQ]

theorem source_product_cap_guard (i : Uniform07.Row) :
    Uniform07.kappa i*Early.bidCap i < Uniform07.entry i := by
  have ht := Uniform07.cutoff_pos i
  cases i <;> norm_num [Uniform07.entry, Uniform07.kappa, Uniform07.kappaQ,
    Early.bidCap, Early.capRatioQ, Uniform07.x, Uniform07.xQ,
    Uniform07.xiQ, Uniform07.etaQ] at * <;> nlinarith

theorem sourceProductProbability_mem (i : Uniform07.Row) {b : ℝ}
    (hb : b ∈ Icc 0 (Early.bidCap i)) :
    sourceProductProbability i b ∈ Icc (0 : ℝ) 1 := by
  by_cases hbl : b ≤ Uniform07.entry i
  · simp [sourceProductProbability, hbl]
  · have hlb : Uniform07.entry i < b := lt_of_not_ge hbl
    have hb0 := (source_entry_pos i).trans hlb
    have hdiv : Uniform07.entry i/b ≤ 1 := (div_le_one hb0).mpr hlb.le
    have hkb : Uniform07.kappa i*b ≤ Uniform07.entry i :=
      ((mul_le_mul_of_nonneg_left hb.2 (source_kappa_pos i).le).trans
        (source_product_cap_guard i).le)
    have hkd : Uniform07.kappa i ≤ Uniform07.entry i/b := (le_div_iff₀ hb0).mpr hkb
    rw [sourceProductProbability, if_neg hbl]
    refine ⟨div_nonneg (by linarith) (Uniform07.xi_pos i).le, ?_⟩
    apply (div_le_one (Uniform07.xi_pos i)).mpr
    linarith [source_kappa_add_xi i]

theorem sourceProductProbability_receipt (i : Uniform07.Row) (b : ℝ) :
    b*sourceProductProbability i b*(1-Uniform07.xi i*sourceProductProbability i b) =
      Uniform07.entry i*sourceProductProbability i b := by
  by_cases hbl : b ≤ Uniform07.entry i
  · simp [sourceProductProbability, hbl]
  · have hb0 := (source_entry_pos i).trans (lt_of_not_ge hbl)
    have he : b*(1-Uniform07.xi i*sourceProductProbability i b) = Uniform07.entry i := by
      rw [sourceProductProbability, if_neg hbl]
      field_simp [hb0.ne', (Uniform07.xi_pos i).ne']
      ring
    nlinarith [congrArg (fun z : ℝ => z*sourceProductProbability i b) he]

def sourceLowerBenchmarkBid (i : Uniform07.Row) (v : ℝ) : ℝ :=
  if Uniform07.entry i < v then Uniform07.entry i*v/
    (Uniform07.kappa i*v+Uniform07.xi i*Uniform07.entry i) else 0

theorem sourceLowerBenchmarkBid_mem (i : Uniform07.Row) {v : ℝ}
    (hv : 0 < v) (hvt : v ≤ Uniform07.cutoff i) :
    sourceLowerBenchmarkBid i v ∈ Icc 0 (Early.bidCap i) := by
  have hκ := source_kappa_pos i
  have hxi := Uniform07.xi_pos i
  have hlam := source_entry_pos i
  have ht := Uniform07.cutoff_pos i
  have hU := (Early.upper_floor_interface i).2.1
  by_cases hvl : Uniform07.entry i < v
  · have hdv : 0 < Uniform07.kappa i*v+Uniform07.xi i*Uniform07.entry i := by
      positivity
    have hdt : 0 < Uniform07.kappa i*Uniform07.cutoff i+
        Uniform07.xi i*Uniform07.entry i := by
      have := source_kappa_pos i
      have := Uniform07.cutoff_pos i
      have := Uniform07.xi_pos i
      have := source_entry_pos i
      positivity
    have hmon : Uniform07.entry i*v/(Uniform07.kappa i*v+Uniform07.xi i*Uniform07.entry i) ≤
        Uniform07.entry i*Uniform07.cutoff i/
          (Uniform07.kappa i*Uniform07.cutoff i+Uniform07.xi i*Uniform07.entry i) := by
      apply (div_le_div_iff₀ hdv hdt).mpr
      have hn : 0 ≤ Uniform07.xi i*(Uniform07.entry i)^2*(Uniform07.cutoff i-v) :=
        mul_nonneg (mul_nonneg (Uniform07.xi_pos i).le (sq_nonneg _)) (sub_nonneg.mpr hvt)
      nlinarith
    rw [sourceLowerBenchmarkBid, if_pos hvl]
    refine ⟨div_nonneg (mul_nonneg (source_entry_pos i).le hv.le) hdv.le, ?_⟩
    rw [Early.cap_literal_product_formula i]
    exact hmon.trans (le_add_of_nonneg_right (by positivity))
  · simp only [sourceLowerBenchmarkBid, if_neg hvl]
    exact ⟨le_rfl, hU.le⟩

theorem sourceLowerBenchmarkBid_probability (i : Uniform07.Row) {v : ℝ} (hv : 0 < v) :
    sourceProductProbability i (sourceLowerBenchmarkBid i v) =
      lowerTargetProbability (Uniform07.entry i) v := by
  have hxi := Uniform07.xi_pos i
  have hκ := source_kappa_pos i
  have hlam := source_entry_pos i
  have hκξ := source_kappa_add_xi i
  by_cases hvl : Uniform07.entry i < v
  · have hd : 0 < Uniform07.kappa i*v+Uniform07.xi i*Uniform07.entry i := by positivity
    have hlb : Uniform07.entry i < sourceLowerBenchmarkBid i v := by
      rw [sourceLowerBenchmarkBid, if_pos hvl]
      apply (lt_div_iff₀ hd).mpr
      have hpos : 0 < Uniform07.xi i*Uniform07.entry i*(v-Uniform07.entry i) := by positivity
      nlinarith [congrArg (fun z : ℝ => z*Uniform07.entry i*v) hκξ]
    have hs : 0 ≤ 1-Uniform07.entry i/v := by
      have := (div_le_one hv).mpr hvl.le
      linarith
    rw [sourceProductProbability, if_neg (not_le.mpr hlb),
      sourceLowerBenchmarkBid, if_pos hvl, lowerTargetProbability, max_eq_left hs]
    field_simp [hv.ne', hlam.ne', hxi.ne', hd.ne']
    nlinarith [congrArg (fun z : ℝ => z*v) hκξ]
  · have hs : 1-Uniform07.entry i/v ≤ 0 := by
      have := (one_le_div hv).mpr (le_of_not_gt hvl)
      linarith
    simp only [sourceLowerBenchmarkBid, if_neg hvl, sourceProductProbability,
      if_pos hlam.le, lowerTargetProbability, max_eq_right hs]

theorem source_lower_target_moments (i : Uniform07.Row) {v : ℝ}
    (hv : 0 < v) (hvt : v < Uniform07.cutoff i) :
    (sourceLimitLaw i v).load = 2*lowerTargetProbability (Uniform07.entry i) v ∧
    (sourceLimitLaw i v).duplicates = (lowerTargetProbability (Uniform07.entry i) v)^2 := by
  by_cases hvl : v < Uniform07.entry i
  · have hs : 1-Uniform07.entry i/v ≤ 0 := by
      have := (one_le_div hv).mpr hvl.le
      linarith
    rw [sourceLimitLaw_below i hvl]
    simp [CountLaw.load, CountLaw.duplicates, CountLaw.success,
      FiniteLaw.expect_dirac, successIndicator, lowerTargetProbability, max_eq_right hs]
  · have hm := source_active_moments i ⟨le_of_not_gt hvl, hvt⟩
    have hs := (active_probability_bounds i (le_of_not_gt hvl)).1
    simpa only [lowerTargetProbability, max_eq_left hs, Uniform07.activeMarginal]
      using ⟨hm.1, hm.2.2⟩

theorem actual_uniform_payoff_moments (row : Uniform07.Row)
    (Γ : FiniteGame m 2 c Seed)
    (hA : Γ.A = Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : Γ.g = 0) (i : Fin m) (v : ℝ) (a : JointAction 2) :
    (problem Γ i).payoff v a =
      (v-a.bid)*((problem Γ i).outcome a).load-
        (v-(1-Uniform07.eta row)*a.bid)*((problem Γ i).outcome a).duplicates := by
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G = _
  rw [CountLaw.utility_eq, hA, hg, CountLaw.charge_affine]
  unfold CountLaw.duplicates
  ring

theorem source_product_payoff_quadratic (row : Uniform07.Row) (v b : ℝ) :
    (v-b)*(2*sourceProductProbability row b)-
      (v-(1-Uniform07.eta row)*b)*(sourceProductProbability row b)^2 =
        lowerProductQuadratic (Uniform07.entry row) v (sourceProductProbability row b) := by
  have hrec := sourceProductProbability_receipt row b
  have hxi := Uniform07.xi_identity row
  rw [← hxi]
  unfold lowerProductQuadratic
  nlinarith

theorem actual_product_payoff_error_of_moments (row : Uniform07.Row)
    (Γ : FiniteGame m 2 c Seed)
    (hA : Γ.A = Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : Γ.g = 0) (i : Fin m) (v ε : ℝ) (hv : 0 ≤ v) (_hε : 0 ≤ ε)
    (b : Icc (0 : ℝ) (Early.bidCap row))
    (hL : |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
      2*sourceProductProbability row b| ≤ ε)
    (hD : |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
      (sourceProductProbability row b)^2| ≤ ε) :
    |(problem Γ i).payoff v (sourceLowerBroadcastAction (Early.bidCap row) b)-
      lowerProductQuadratic (Uniform07.entry row) v (sourceProductProbability row b)| ≤
        2*(v+Early.bidCap row)*ε := by
  let P := (problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)
  let p := sourceProductProbability row b
  have he : (problem Γ i).payoff v (sourceLowerBroadcastAction (Early.bidCap row) b)-
      lowerProductQuadratic (Uniform07.entry row) v p =
      (v-(b : ℝ))*(P.load-2*p)-
        (v-(1-Uniform07.eta row)*(b : ℝ))*(P.duplicates-p^2) := by
    rw [actual_uniform_payoff_moments row Γ hA hg]
    have hpoly := source_product_payoff_quadratic row v b
    change (v-(b : ℝ))*P.load-(v-(1-Uniform07.eta row)*(b : ℝ))*P.duplicates-
      lowerProductQuadratic (Uniform07.entry row) v p = _
    rw [← hpoly]
    ring
  have hη0 := (Uniform07.eta_pos row).le
  have hη1 := sourceProduct_eta_le_one row
  have hU := (Early.upper_floor_interface row).2.1
  have hc0 : 0 ≤ (1-Uniform07.eta row)*(b : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hη1) b.2.1
  have hcU : (1-Uniform07.eta row)*(b : ℝ) ≤ Early.bidCap row :=
    (mul_le_of_le_one_left b.2.1 (by linarith)).trans b.2.2
  have hvb : |v-(b : ℝ)| ≤ v+Early.bidCap row :=
    abs_le.mpr ⟨by linarith [b.2.2], by linarith [b.2.1]⟩
  have hvc : |v-(1-Uniform07.eta row)*(b : ℝ)| ≤ v+Early.bidCap row :=
    abs_le.mpr ⟨by linarith, by linarith [(Early.upper_floor_interface row).2.1]⟩
  rw [he]
  calc
    _ ≤ |(v-(b : ℝ))*(P.load-2*p)|+
        |(v-(1-Uniform07.eta row)*(b : ℝ))*(P.duplicates-p^2)| := abs_sub _ _
    _ = |v-(b : ℝ)| *|P.load-2*p|+
        |v-(1-Uniform07.eta row)*(b : ℝ)| *|P.duplicates-p^2| := by rw [abs_mul, abs_mul]
    _ ≤ (v+Early.bidCap row)*ε+(v+Early.bidCap row)*ε :=
      add_le_add (mul_le_mul hvb hL (abs_nonneg _) (by positivity))
        (mul_le_mul hvc hD (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem two_moment_error_of_probability_error (P : CountLaw 2)
    {p q ε d : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hL : |P.load-2*p| ≤ ε) (hD : |P.duplicates-p^2| ≤ ε)
    (hpq : |p-q| ≤ d) :
    |P.load-2*q| ≤ ε+2*d ∧ |P.duplicates-q^2| ≤ ε+2*d := by
  have hs : |p^2-q^2| ≤ 2*d := by
    have hh := Uniform07.conditional_product_error hq hp hp
    rw [← pow_two] at hh
    linarith
  constructor
  · have he : P.load-2*q = (P.load-2*p)+2*(p-q) := by ring
    rw [he]
    have ht := abs_add_le (P.load-2*p) (2*(p-q))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith
  · have he : P.duplicates-q^2 = (P.duplicates-p^2)+(p^2-q^2) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hD hs)

theorem actual_lower_best_response_mass_error (row : Uniform07.Row)
    (Γ : FiniteGame m 2 c Seed)
    (hA : Γ.A = Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : Γ.g = 0) (i : Fin m) (v ε : ℝ)
    (hv : 0 < v) (hvt : v < Uniform07.cutoff row) (hε : 0 ≤ ε)
    (hmom : ∀ b : Icc (0 : ℝ) (Early.bidCap row),
      |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b| ≤ ε ∧
      |((problem Γ i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2| ≤ ε)
    (a : JointAction 2) (ha : a.bid ≤ Early.bidCap row) (hr : a.routeCount = 2)
    (hbr : ∀ a' : JointAction 2, (problem Γ i).payoff v a' ≤ (problem Γ i).payoff v a)
    (r : Fin 3) :
    |((problem Γ i).outcome a).mass r-(sourceLimitLaw row v).mass r| ≤
      3*(ε+2*Real.sqrt (4*(v+Early.bidCap row)*ε/v)) := by
  let b : Icc (0 : ℝ) (Early.bidCap row) := ⟨a.bid, a.bid_nonneg, ha⟩
  have hb : sourceLowerBroadcastAction (Early.bidCap row) b = a :=
    sourceLowerBroadcastAction_eq _ a ha hr
  let b₀ : Icc (0 : ℝ) (Early.bidCap row) :=
    ⟨sourceLowerBenchmarkBid row v, sourceLowerBenchmarkBid_mem row hv hvt.le⟩
  let a₀ := sourceLowerBroadcastAction (Early.bidCap row) b₀
  let e := 2*(v+Early.bidCap row)*ε
  have he0 : 0 ≤ e := by
    have hU := (Early.upper_floor_interface row).2.1
    dsimp [e]
    positivity
  have hbpay := actual_product_payoff_error_of_moments row Γ hA hg i v ε hv.le hε
    b (hmom b).1 (hmom b).2
  have h₀pay := actual_product_payoff_error_of_moments row Γ hA hg i v ε hv.le hε
    b₀ (hmom b₀).1 (hmom b₀).2
  have hp₀ : sourceProductProbability row (b₀ : ℝ) =
      lowerTargetProbability (Uniform07.entry row) v := sourceLowerBenchmarkBid_probability row hv
  rw [hp₀] at h₀pay
  have htest : lowerProductQuadratic (Uniform07.entry row) v
      (lowerTargetProbability (Uniform07.entry row) v)-e ≤ (problem Γ i).payoff v a₀ := by
    have hh := (abs_le.mp h₀pay).1
    linarith
  have hp := sourceProductProbability_mem row b.2
  have hpq := actual_best_response_probability_error Γ i v (Uniform07.entry row)
    (sourceProductProbability row b) e hv hp.1 he0 a a₀ hbr
      (by simpa only [hb] using hbpay) htest
  have hroot : 2*e/v = 4*(v+Early.bidCap row)*ε/v := by dsimp [e]; ring
  rw [hroot] at hpq
  have hM := two_moment_error_of_probability_error ((problem Γ i).outcome a) hp
    (lowerTargetProbability_mem (source_entry_pos row).le hv)
    (by simpa only [hb] using (hmom b).1)
    (by simpa only [hb] using (hmom b).2) hpq
  have hQ := source_lower_target_moments row hv hvt
  apply two_count_mass_error _ _ (by positivity)
  · simpa only [hQ.1] using hM.1
  · simpa only [hQ.2] using hM.2

theorem actual_lower_conditional_count_limit (row : Uniform07.Row)
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) 2 (C k) Seed)
    (hM : ∀ k, 0 < M k)
    (hA : ∀ k, (Γ k).A = Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (sourceProduct_eta_le_one row))
    (hg : ∀ k, (Γ k).g = 0)
    (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hmom : ∀ᶠ k in atTop, ∀ i : Fin (M k), ∀ b : Icc (0 : ℝ) (Early.bidCap row),
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b| ≤ ε k ∧
      |((problem (Γ k) i).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2| ≤ ε k)
    (hversion : ∀ v : ℝ, 0 < v → v < Uniform07.cutoff row → ∀ k,
      ∀ᵐ a ∂(Γ k).σ v, a.bid ≤ Early.bidCap row ∧ a.routeCount = 2 ∧
        ∀ i : Fin (M k), ∀ a' : JointAction 2,
          (problem (Γ k) i).payoff v a' ≤ (problem (Γ k) i).payoff v a) :
    ∀ v : ℝ, 0 < v → v < Uniform07.cutoff row → ∀ r : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hM k) v).mass r)
        atTop (𝓝 (sourceLimitMass row v r)) := by
  intro v hv hvt r
  let err : ℕ → ℝ := fun k => 3*(ε k+2*Real.sqrt (4*(v+Early.bidCap row)*ε k/v))
  have hs : Tendsto (fun k => Real.sqrt (4*(v+Early.bidCap row)*ε k/v)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, Real.sqrt_zero] using
      ((hε.const_mul (4*(v+Early.bidCap row))).div_const v).sqrt
  have he : Tendsto err atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hε.add (hs.const_mul 2)).const_mul 3
  rw [← sourceLimitLaw_mass row v r]
  apply actual_conditional_mass_tendsto_of_error M C Γ hM v (sourceLimitLaw row v) err he
  filter_upwards [hmom] with k hk
  intro i
  filter_upwards [hversion v hv hvt k] with a ha
  intro r
  exact actual_lower_best_response_mass_error row (Γ k) (hA k) (hg k) i v (ε k)
    hv hvt (hε0 k) (hk i) a ha.1 ha.2.1 (ha.2.2 i) r

def upperSingletonMass (q : ℝ) (r : Fin 3) : ℝ :=
  if r.val = 0 then 1-q else if r.val = 1 then q else 0

theorem actual_singleton_mass (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) (ha : a.routeCount = 1) (r : Fin 3) :
    ((problem Γ i).outcome a).mass r = upperSingletonMass (meanAcceptProb Γ i a.bid) r := by
  let P := (problem Γ i).outcome a
  have hLS : P.load ≤ P.success := by
    have hh := load_le_routeCount_mul_success Γ i a
    simpa only [ha, Nat.cast_one, one_mul] using hh
  have hD : P.duplicates = 0 := by
    unfold CountLaw.duplicates
    exact sub_eq_zero.mpr (le_antisymm hLS P.success_le_load)
  have hL : P.load = meanAcceptProb Γ i a.bid := by
    have hh := load_eq_mean Γ (by norm_num : 0 < 2) i a
    simpa only [ha, Nat.cast_one, one_mul] using hh
  have hf := two_count_mass_formulas P
  fin_cases r
  · simpa [hL, hD, upperSingletonMass] using hf.1
  · simpa [hL, hD, upperSingletonMass] using hf.2.1
  · simpa [hD, upperSingletonMass] using hf.2.2

theorem actual_upper_conditional_mass (Γ : FiniteGame m 2 c Seed) (hm : 0 < m)
    (v q : ℝ) (a : JointAction 2) (ha : a.routeCount = 1)
    (hσ : Γ.σ v = Measure.dirac a)
    (hq : ∀ i : Fin m, meanAcceptProb Γ i a.bid = q) (r : Fin 3) :
    (conditionalTypeCountLaw Γ hm v).mass r = upperSingletonMass q r := by
  have hi (i : Fin m) : (typeOutcome Γ i v).mass r = upperSingletonMass q r := by
    change (∫ a', ((problem Γ i).outcome a').mass r ∂Γ.σ v) = _
    rw [hσ, integral_dirac, actual_singleton_mass Γ i a ha, hq i]
  change (∑ i, (typeOutcome Γ i v).mass r)/(m : ℝ) = _
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hmR]

theorem actual_upper_conditional_count_limit (row : Uniform07.Row)
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) 2 (C k) Seed)
    (hM : ∀ k, 0 < M k) (hM_top : Tendsto M atTop atTop)
    (v : ℝ) (hv : Uniform07.cutoff row ≤ v)
    (a : ℕ → JointAction 2) (ha : ∀ k, (a k).routeCount = 1)
    (hσ : ∀ k, (Γ k).σ v = Measure.dirac (a k))
    (hq : ∀ k (i : Fin (M k)), meanAcceptProb (Γ k) i (a k).bid =
      source_upper_rank row (M k) v) (r : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (hM k) v).mass r)
      atTop (𝓝 (sourceLimitMass row v r)) := by
  have hq_top := (source_upper_rank_tendsto_one_at row hv).comp hM_top
  have hcont : Continuous (fun q : ℝ => upperSingletonMass q r) := by
    fin_cases r <;> norm_num [upperSingletonMass] <;> fun_prop
  have ht := (hcont.tendsto 1).comp hq_top
  have he : (fun k => (conditionalTypeCountLaw (Γ k) (hM k) v).mass r) =
      fun k => upperSingletonMass (source_upper_rank row (M k) v) r := by
    funext k
    exact actual_upper_conditional_mass (Γ k) (hM k) v _ (a k) (ha k) (hσ k) (hq k) r
  rw [he]
  have hlamv : Uniform07.entry row ≤ v := (source_entry_lt_cutoff row).le.trans hv
  have hmass : upperSingletonMass 1 r = sourceLimitMass row v r := by
    fin_cases r <;> simp [upperSingletonMass, sourceLimitMass,
      not_lt.mpr hlamv, not_lt.mpr hv]
  rw [← hmass]
  exact ht

end FCAppendix.Affine.Uniform07Finishing
