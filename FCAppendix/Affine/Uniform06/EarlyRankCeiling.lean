import FCAppendix.Affine.Uniform06.ReceiptGap
import FCAppendix.Affine.Uniform06.PureRankCounts
import FCAppendix.Affine.Uniform06.RankCutoff

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyRankCeiling

open MeasureTheory Set Filter
open FCAppendix.Affine.Uniform07 ActiveGraphComponent

theorem conditional_value_scaled_cdf (i : Row) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) (cutoff i)) :
    cutoff i*(LowChernoff.conditionalValueLaw i).real (Iic s)=s := by
  have he : Iic s ∩ Icc (0:ℝ) (cutoff i)=Icc (0:ℝ) s := by
    ext v
    constructor
    · intro hv
      exact ⟨hv.2.1,hv.1⟩
    · intro hv
      exact ⟨hv.2,hv.1,hv.2.trans hs.2⟩
  rw [measureReal_def,LowChernoff.conditionalValueLaw,Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic,he,Real.volume_Icc]
  simp only [smul_eq_mul,sub_zero,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (one_div_pos.mpr (cutoff_pos i)).le,ENNReal.toReal_ofReal hs.1]
  field_simp [(cutoff_pos i).ne']

theorem same_joint_value_support (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i) :
    ∀ᵐ p ∂G, p.1 ∈ Icc (0:ℝ) (cutoff i) := by
  apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
  rw [hvalue,LowChernoff.conditionalValueLaw]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem rank_ceiling_of_active_exclusion (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {s B : ℝ} (hs : s ∈ Icc (0:ℝ) (cutoff i))
    (hexclude : ∀ᵐ p ∂G, p.1 ∈ Ioc s (cutoff i) → B < p.2) :
    ∀ b ≤ B, PureRankCounts.sourceRank (cutoff i) (G.map Prod.snd) b ≤ s := by
  intro b hb
  let A : Set (ℝ × ℝ) := {p | p.2 ≤ b}
  let V : Set (ℝ × ℝ) := {p | p.1 ≤ s}
  have hsub : A ≤ᵐ[G] V := by
    filter_upwards [same_joint_value_support i G hvalue,hexclude] with p hp he hpA
    change p.1 ≤ s
    by_contra hn
    have hs' : s < p.1 := lt_of_not_ge hn
    have hb' := he ⟨hs',hp.2⟩
    change p.2 ≤ b at hpA
    linarith
  have hmass : (G.map Prod.snd).real (Iic b) ≤ (G.map Prod.fst).real (Iic s) := by
    rw [measureReal_def,Measure.map_apply measurable_snd measurableSet_Iic,
      measureReal_def,Measure.map_apply measurable_fst measurableSet_Iic]
    exact ENNReal.toReal_mono (measure_ne_top G _) (measure_mono_ae hsub)
  have hscaled := mul_le_mul_of_nonneg_left hmass (cutoff_pos i).le
  rw [hvalue,conditional_value_scaled_cdf i hs] at hscaled
  exact hscaled

theorem activeBid_monotone_positive (i : Row) : MonotoneOn (activeBid i) (Ioi (0:ℝ)) := by
  intro v hv w hw hvw
  have he : 0 < entry i := by
    unfold entry
    exact mul_pos (by cases i <;> norm_num [x,xQ]) (cutoff_pos i)
  have hk : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hvd : 0 < kappa i*v+xi i*entry i := add_pos (mul_pos hk hv) (mul_pos (xi_pos i) he)
  have hwd : 0 < kappa i*w+xi i*entry i := add_pos (mul_pos hk hw) (mul_pos (xi_pos i) he)
  unfold activeBid
  apply (div_le_div_iff₀ hvd hwd).mpr
  have hh := mul_nonneg (mul_nonneg (xi_pos i).le (sq_nonneg (entry i)))
    (sub_nonneg.mpr hvw)
  nlinarith

def ceilingValue (i : Row) : ℝ := (x i+1/400)*cutoff i
def prefixEnd (i : Row) : ℝ := entry i+cutoff i/10000

theorem ceilingValue_bounds (i : Row) :
    ceilingValue i ∈ Ioo (entry i) (cutoff i) ∧
      ceilingValue i < RankCutoff.Mstar i := by
  have h0 : 0 < x i := by cases i <;> norm_num [x,xQ]
  have h1 : x i+1/400 < 1 := by cases i <;> norm_num [x,xQ]
  have ht := cutoff_pos i
  unfold ceilingValue entry RankCutoff.Mstar
  constructor
  · constructor
    · nlinarith
    · simpa using mul_lt_mul_of_pos_right h1 ht
  · nlinarith

theorem active_at_ceiling (i : Row) :
    entry i+cutoff i/2000 < activeBid i (ceilingValue i) := by
  have hx : 0 < x i+1/400 := by cases i <;> norm_num [x,xQ]
  have hr : x i+1/2000 < x i*(x i+1/400)/(kappa i*(x i+1/400)+xi i*x i) := by
    cases i <;> norm_num [x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
  have hs := activeBid_scaled i hx
  rw [show cutoff i*(x i+1/400)=ceilingValue i by unfold ceilingValue; ring] at hs
  rw [hs]
  have hh := mul_lt_mul_of_pos_left hr (cutoff_pos i)
  simpa [entry,div_eq_mul_inv,mul_add,mul_comm,mul_left_comm,mul_assoc] using hh

theorem source_early_rank_ceiling (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Ioc (ceilingValue i) (cutoff i) →
      |p.2-activeBid i p.1| ≤ cutoff i/10000) :
    ∀ b ≤ prefixEnd i,
      PureRankCounts.sourceRank (cutoff i) (G.map Prod.snd) b < RankCutoff.Mstar i := by
  have he : 0 < entry i := mul_pos
    (by cases i <;> norm_num [x,xQ]) (cutoff_pos i)
  have hs := ceilingValue_bounds i
  have hex : ∀ᵐ p ∂G, p.1 ∈ Ioc (ceilingValue i) (cutoff i) → prefixEnd i < p.2 := by
    filter_upwards [hactive] with p hp hpI
    have hmono := activeBid_monotone_positive i
      (he.trans hs.1.1) (he.trans (hs.1.1.trans hpI.1)) hpI.1.le
    have ha := active_at_ceiling i
    have herr := (abs_le.mp (hp hpI)).1
    have ht := cutoff_pos i
    unfold prefixEnd
    linarith
  intro b hb
  exact (rank_ceiling_of_active_exclusion i G hvalue
    ⟨(he.trans hs.1.1).le,hs.1.2.le⟩ hex b hb).trans_lt hs.2

theorem eventually_source_early_rank_ceiling (i : Row)
    (G : ℕ → Measure (ℝ × ℝ)) [∀ m, IsProbabilityMeasure (G m)]
    (hvalue : ∀ m, (G m).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hactive : ∀ᶠ m in atTop, ∀ᵐ p ∂G m, p.1 ∈ Ioc (ceilingValue i) (cutoff i) →
      |p.2-activeBid i p.1| ≤ cutoff i/10000) :
    ∀ᶠ m in atTop, ∀ b ≤ prefixEnd i,
      PureRankCounts.sourceRank (cutoff i) ((G m).map Prod.snd) b < RankCutoff.Mstar i := by
  filter_upwards [hactive] with m hm
  exact source_early_rank_ceiling i (G m) (hvalue m) hm

end FCAppendix.Affine.Uniform06.EarlyRankCeiling
