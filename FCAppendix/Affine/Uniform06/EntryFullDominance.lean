import FCAppendix.Affine.Uniform06.EntryFullRestoration

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryFullDominance

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition EntryLiteralCanonicalTransfer
open EntryConstructedSource EntryConstructedSource.EarlyArray EntryFiniteConstructor
open EntryProducedMoments EntryGoodOptimizer EntryFullRestoration

lemma scalar_payoff_errors {η t v b S D Q R e : ℝ}
    (hη : η∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) v) (hvt : v≤ t)
    (hS : S-(2*Q-R)∈Icc (0:ℝ) e) (hD : D-R∈Icc (0:ℝ) e) :
    (v-b)*(S+D)/2-(v-b)*Q≤ t*e ∧
      (2*(v-b)*Q-((v-b)+η*b)*R)-((v-b)*S-η*b*D)≤ t*e := by
  let A := S-(2*Q-R)
  let B := D-R
  have he : 0≤ e := hS.1.trans hS.2
  have hsur : 0≤ v-b := sub_nonneg.mpr hb.2
  have hab : A+B≤2*e := by dsimp [A,B]; linarith [hS.2,hD.2]
  have hsum := mul_le_mul_of_nonneg_left hab hsur
  have hupper := mul_le_mul_of_nonneg_right (show v-b≤ t by linarith [hb.1]) he
  have hpen : 0≤η*b ∧ η*b≤ t := by
    refine ⟨mul_nonneg hη.1 hb.1,?_⟩
    have hh := mul_le_mul_of_nonneg_right hη.2 hb.1
    linarith
  have hB := mul_le_mul_of_nonneg_left hD.2 hpen.1
  have hA := mul_nonneg hsur hS.1
  have hpenE := mul_le_mul_of_nonneg_right hpen.2 he
  dsimp only [A,B] at *
  constructor <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : EarlyArray μ i)

def oneFull (cm : (m : ℕ)→(Fin (s.population m-1)→ Fin 4)→ℝ)
    (v : ℕ→ℝ) (m : ℕ) (b : ℝ) : ℝ :=
  (v m-b)*(sourceSuccess i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b+
    sourceDuplicate i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b)/2

def twoFull (cm : (m : ℕ)→(Fin (s.population m-1)→ Fin 4)→ℝ)
    (v : ℕ→ℝ) (m : ℕ) (b : ℝ) : ℝ :=
  (v m-b)*sourceSuccess i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b-
    eta i*b*sourceDuplicate i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b

def error (m : ℕ) : ℝ :=
  18*cutoff i*Real.exp (-2*((s.population m-1:ℕ):ℝ)*(epsilon i)^2)

theorem eventual_payoff_errors (cm : (m : ℕ)→(Fin (s.population m-1)→ Fin 4)→ℝ)
    (hc : ∀ m,CountContract i (s.guards m) (cm m)) (v : ℕ→ℝ)
    (hv : Tendsto v atTop (𝓝 (entry i))) :
    ∀ᶠ m in atTop,∀ b∈Icc (0:ℝ) (v m),
      oneFull s cm v m b-one s v m b≤ error s m ∧
      two s v m b-twoFull s cm v m b≤ error s m := by
  have ht := cutoff_pos i
  have hbEntry : entry i∈band i := by
    unfold band SourcePrefixConstructor.radius
    constructor <;> linarith
  filter_upwards [s.eventually_inputs,hv.eventually_lt_const (EarlyMean.entry_lt_cutoff i)] with m hm hvt
  have h := hm.2 (entry i) hbEntry
  have hker := full_kernel_error i (s.jointLaw m) (s.guards m) (cm m) (hc m) h
  intro b hb
  have hh := scalar_payoff_errors
    (show eta i∈Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ]) hb hvt.le
      (hker b).1 (hker b).2
  simpa only [oneFull,twoFull,one,two,EntryProducedMoments.first,second,sourceSuccess,sourceDuplicate,error,
    mul_assoc,mul_left_comm,mul_comm] using hh

theorem error_negligible_at_optimizer (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i))) :
    ∀ᶠ m in atTop,2*error s m< EntrySourceGap.margin i*one s v m (chosen s v m) := by
  have hε := (epsilon_bounds i).1
  have hδ := EntrySourceGap.margin_pos i
  have hN : Tendsto (fun m => s.population m-1) atTop atTop := by
    simpa only [Function.comp_def] using PhysicalRates.rivals_tendsto.comp s.population_tendsto
  have hdecay : Tendsto (fun m => 36*cutoff i*Real.exp
      (-(epsilon i)^2*((s.population m-1:ℕ):ℝ))) atTop (𝓝 (0:ℝ)) := by
    have hh := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp
        ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop (sq_pos_of_pos hε)))
    simpa only [mul_zero,Function.comp_def,neg_mul] using hh.const_mul (36*cutoff i)
  filter_upwards [chosen_subexponential s v hv ((epsilon i)^2) (sq_pos_of_pos hε),
    hdecay.eventually_lt_const hδ] with m hU he
  have hmul := mul_lt_mul_of_pos_right he
    (Real.exp_pos (-(epsilon i)^2*((s.population m-1:ℕ):ℝ)))
  have hex : Real.exp (-(epsilon i)^2*((s.population m-1:ℕ):ℝ))*
      Real.exp (-(epsilon i)^2*((s.population m-1:ℕ):ℝ))=
      Real.exp (-2*((s.population m-1:ℕ):ℝ)*(epsilon i)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh : 2*error s m< EntrySourceGap.margin i*
      Real.exp (-(epsilon i)^2*((s.population m-1:ℕ):ℝ)) := by
    rw [mul_assoc (36*cutoff i),hex] at hmul
    unfold error
    nlinarith only [hmul]
  exact hh.trans_le (mul_le_mul_of_nonneg_left hU hδ.le)

theorem floor_zero_below (i : Row) {v : ℝ} (hv : v≤ entry i+cutoff i/400) :
    LowChernoff.physicalFloor i v=0 := by
  have ht := cutoff_pos i
  have hr : (v-(entry i+cutoff i/400))/(cutoff i/400)≤0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (by positivity)
  unfold LowChernoff.physicalFloor
  rw [max_eq_left hr]
  norm_num

theorem original_full_entry_dominance
    (cm : (m : ℕ)→(Fin (s.population m-1)→ Fin 4)→ℝ)
    (hc : ∀ m,CountContract i (s.guards m) (cm m))
    (v : ℕ→ℝ) (hv : Tendsto v atTop (𝓝 (entry i)))
    (hnull : ∀ m,∀ z : ℝ,((s.jointLaw m).map Prod.snd) {z}=0) :
    ∀ᶠ m in atTop,
      chosen s v m∈Icc (LowChernoff.physicalFloor i (v m)) (min (v m) (ReceiptGap.cap i)) ∧
      0< twoFull s cm v m (chosen s v m) ∧
      ∀ b : ℝ,0≤ b → oneFull s cm v m b< twoFull s cm v m (chosen s v m) := by
  have ht := cutoff_pos i
  have hδ := EntrySourceGap.margin_pos i
  have hlo : 0< lowerPrice i := by
    have hx : (7/10:ℝ)≤ x i := by cases i <;> norm_num [x,xQ]
    unfold lowerPrice entry
    nlinarith
  filter_upwards [actual_optimizer_advantage s v hv hnull,eventually_optimizer s v hv,
    eventual_payoff_errors s cm hc v hv,error_negligible_at_optimizer s v hv,
    hv.eventually_lt_const (ReceiptGap.entry_below_cap i),
    hv.eventually_lt_const (show entry i< entry i+cutoff i/400 by linarith)]
    with m hgood hopt herr hsmall hvc hvfloor
  have hb : chosen s v m∈Icc (0:ℝ) (v m) := ⟨hlo.le.trans hopt.1.1.1,hopt.1.1.2⟩
  obtain ⟨dq,hd,hFOC,hfactor⟩ := hgood.2.2
  have htwo := (herr (chosen s v m) hb).2
  have he : 0≤ error s m := by unfold error; positivity
  have hpos : 0< twoFull s cm v m (chosen s v m) := by nlinarith [hgood.1]
  refine ⟨?_,hpos,?_⟩
  · rw [floor_zero_below i hvfloor.le,min_eq_left hvc.le]
    exact hb
  · intro b hb0
    by_cases hbv : b≤ v m
    · have hsingle := (herr b ⟨hb0,hbv⟩).1
      have hmax := hgood.2.1 b ⟨hb0,hbv⟩
      nlinarith
    · have hSD := source_first_duplicate_bounds i (s.population m) (s.jointLaw m)
        (s.guards m) (cm m) b
      have hnon : 0≤ sourceSuccess i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b+
          sourceDuplicate i (s.population m) (s.jointLaw m) (s.guards m) (cm m) b :=
        add_nonneg hSD.1.1 hSD.2.1
      have hs : oneFull s cm v m b≤0 := by
        unfold oneFull
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hnon) (by norm_num)
      exact hs.trans_lt hpos

end FCAppendix.Affine.Uniform06.EntryFullDominance
