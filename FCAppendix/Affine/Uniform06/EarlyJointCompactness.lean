import FCAppendix.Affine.Uniform06.ActiveGraphComponent
import FCAppendix.Affine.Uniform06.LowChernoffSource
import FCAppendix.Affine.Uniform06.ReceiptGap
import FCAppendix.Existence.R01External.FixedMarginal
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyJointCompactness

open MeasureTheory Set Filter Topology
open Uniform07
open scoped NNReal ENNReal

def supportedOn (K : Set (ℝ × ℝ)) : Set (ProbabilityMeasure (ℝ × ℝ)) :=
  {μ | ∀ᵐ p ∂(μ:Measure (ℝ × ℝ)),p ∈ K}

theorem isCompact_supportedOn {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    IsCompact (supportedOn K) := by
  have hc := isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ : ℕ => (0:ℝ≥0)) (K := fun _ : ℕ => K)
    tendsto_const_nhds (fun _ => hK) (Or.inl inferInstance)
  have he : supportedOn K={μ : ProbabilityMeasure (ℝ × ℝ) | ∀ n : ℕ, μ Kᶜ ≤ (0:ℝ≥0)} := by
    ext μ
    constructor
    · intro h n
      change ∀ᵐ p ∂(μ:Measure (ℝ × ℝ)), p ∈ K at h
      have hz : (μ:Measure (ℝ × ℝ)) Kᶜ=0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        simpa only [mem_compl_iff,not_not] using h
      change ((μ:Measure (ℝ × ℝ)) Kᶜ).toNNReal ≤ 0
      rw [hz]
      simp
    · intro h
      have hz : ((μ:Measure (ℝ × ℝ)) Kᶜ).toNNReal=0 :=
        le_antisymm (h 0) bot_le
      have hz' : (μ:Measure (ℝ × ℝ)) Kᶜ=0 := by
        have he := congrArg (fun x : ℝ≥0 => (x:ℝ≥0∞)) hz
        simpa only [ENNReal.coe_toNNReal (measure_ne_top _ _),ENNReal.coe_zero] using he
      have ha := measure_eq_zero_iff_ae_notMem.mp hz'
      change ∀ᵐ p ∂(μ:Measure (ℝ × ℝ)), p ∈ K
      simpa only [mem_compl_iff,not_not] using ha
  rw [he]
  exact hc

theorem limit_supportedOn {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hs : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ K) :
    ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p ∈ K :=
  (isCompact_supportedOn hK).isClosed.mem_of_tendsto hG hs

def box (t U : ℝ) : Set (ℝ × ℝ) := Icc (0:ℝ) t ×ˢ Icc (0:ℝ) U

theorem box_compact (t U : ℝ) : IsCompact (box t U) := isCompact_Icc.prod isCompact_Icc

theorem exists_joint_subsequence (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    {t U : ℝ} (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box t U) :
    ∃ G0 : ProbabilityMeasure (ℝ × ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (G ∘ φ) atTop (𝓝 G0) ∧
      ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p ∈ box t U := by
  obtain ⟨G0,hG0,φ,hφ,hlim⟩ := (isCompact_supportedOn (box_compact t U)).isSeqCompact hbox
  exact ⟨G0,φ,hφ,hlim,hG0⟩

theorem original_marginal_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hv : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i) :
    (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i := by
  haveI : IsProbabilityMeasure (LowChernoff.conditionalValueLaw i) := by
    rw [← hv 0]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  exact (isClosed_fixedFstMarginal (A := ℝ) (LowChernoff.conditionalValueLaw i)).mem_of_tendsto
    hG (Eventually.of_forall hv)

theorem below_value_limit (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (G0 : ProbabilityMeasure (ℝ × ℝ)) {t U : ℝ}
    (hG : Tendsto G atTop (𝓝 G0))
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box t U)
    (hb : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1) :
    ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.2 ≤ p.1 := by
  have hc : IsCompact (box t U ∩ {p : ℝ × ℝ | p.2 ≤ p.1}) :=
    (box_compact t U).inter_right (isClosed_le continuous_snd continuous_fst)
  have hh := limit_supportedOn hc G G0 hG (Eventually.of_forall fun n => by
    filter_upwards [hbox n,hb n] with p hp hpb
    exact ⟨hp,hpb⟩)
  exact hh.mono fun _ h => h.2

def extendedActive (i : Row) (v : ℝ) : ℝ :=
  entry i*max 0 v/((1-xi i)*max 0 v+xi i*entry i)

theorem continuous_extendedActive (i : Row) : Continuous (extendedActive i) := by
  unfold extendedActive
  apply (continuous_const.mul (continuous_const.max continuous_id)).div
    ((continuous_const.mul (continuous_const.max continuous_id)).add continuous_const)
  intro v
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hl := EarlyMean.entry_pos i
  have hn := mul_nonneg (sub_pos.mpr hξ1).le (le_max_left (0:ℝ) v)
  change (1-xi i)*max 0 v+xi i*entry i ≠ 0
  exact ne_of_gt (add_pos_of_nonneg_of_pos hn (mul_pos hξ hl))

theorem extendedActive_eq (i : Row) {v : ℝ} (hv : 0 ≤ v) :
    extendedActive i v=ActiveGraphComponent.activeBid i v := by
  rw [extendedActive,max_eq_right hv]
  simp only [ActiveGraphComponent.activeBid,ReceiptGap.kappa_eq_one_sub]

def activeTolerance (i : Row) (a e : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ entry i+a ∨ |p.2-extendedActive i p.1| ≤ e}

theorem activeTolerance_closed (i : Row) (a e : ℝ) : IsClosed (activeTolerance i a e) := by
  exact (isClosed_le continuous_fst continuous_const).union
    (isClosed_le ((continuous_snd.sub ((continuous_extendedActive i).comp continuous_fst)).abs)
      continuous_const)

theorem active_graph_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    {U : ℝ} (hG : Tendsto G atTop (𝓝 G0))
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box (cutoff i) U)
    (ha : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e) :
    ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1 := by
  have ht (k : ℕ) :
      ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p ∈ box (cutoff i) U ∩
        activeTolerance i (1/((k:ℝ)+1)) (1/((k:ℝ)+1)) := by
    apply limit_supportedOn ((box_compact _ _).inter_right (activeTolerance_closed _ _ _)) G G0 hG
    filter_upwards [ha (1/((k:ℝ)+1)) (by positivity) (1/((k:ℝ)+1)) (by positivity)]
      with n hn
    filter_upwards [hbox n,hn] with p hp hpa
    refine ⟨hp,?_⟩
    by_cases h : p.1 ≤ entry i+1/((k:ℝ)+1)
    · exact Or.inl h
    · exact Or.inr (by rw [extendedActive_eq i hp.1.1]; exact hpa ⟨lt_of_not_ge h,hp.1.2⟩)
  filter_upwards [ae_all_iff.mpr ht] with p hp hv
  have hbelow : 0 ≤ p.1 := (hp 0).1.1.1
  have habs : |p.2-ActiveGraphComponent.activeBid i p.1|=0 := by
    apply le_antisymm _ (abs_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    let d := min (p.1-entry i) ε
    have hd : 0 < d := lt_min (sub_pos.mpr hv.1) hε
    obtain ⟨k,hk⟩ := exists_nat_gt (1/d)
    have he : 1/((k:ℝ)+1) < d := by
      apply (div_lt_iff₀ (by positivity : 0 < (k:ℝ)+1)).mpr
      have hm := (div_lt_iff₀ hd).mp hk
      nlinarith
    have hleft : ¬ p.1 ≤ entry i+1/((k:ℝ)+1) := by
      have hh := he.trans_le (min_le_left _ _)
      linarith
    have hright := ((hp k).2).resolve_left hleft
    rw [extendedActive_eq i hbelow] at hright
    have hh := he.trans_le (min_le_right _ _)
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

theorem exists_early_joint_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hv : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box (cutoff i) (ReceiptGap.cap i))
    (hb : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (ha : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e) :
    ∃ G0 : ProbabilityMeasure (ℝ × ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (G ∘ φ) atTop (𝓝 G0) ∧
      (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i ∧
      (∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.2 ≤ p.1) ∧
      (∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i) (cutoff i) →
        p.2=ActiveGraphComponent.activeBid i p.1) := by
  obtain ⟨G0,φ,hφ,hlim,_⟩ := exists_joint_subsequence G hbox
  refine ⟨G0,φ,hφ,hlim,original_marginal_limit i _ _ hlim (fun n => hv (φ n)),
    below_value_limit _ _ hlim (fun n => hbox (φ n)) (fun n => hb (φ n)),?_⟩
  apply active_graph_limit i _ _ hlim (fun n => hbox (φ n))
  intro a ha' e he
  exact hφ.tendsto_atTop.eventually (ha a ha' e he)

end FCAppendix.Affine.Uniform06.EarlyJointCompactness
