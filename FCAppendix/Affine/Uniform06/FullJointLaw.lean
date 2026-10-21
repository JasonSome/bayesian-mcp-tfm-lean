import FCAppendix.Affine.Uniform06.InactiveFamily
import FCAppendix.Affine.Uniform07.SourceAcceptance

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullJointLaw
open MeasureTheory Set Filter Topology
open Uniform07 EarlyJointCompactness

def bid (i : Row) (v : ℝ) : ℝ := if v ≤ entry i then v else extendedActive i v

theorem measurable_bid (i : Row) : Measurable (bid i) :=
  Measurable.ite measurableSet_Iic measurable_id (continuous_extendedActive i).measurable

theorem conditional_value_probability (i : Row) : IsProbabilityMeasure (LowChernoff.conditionalValueLaw i) := by
  constructor
  rw [LowChernoff.conditionalValueLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,
    Real.volume_Icc,sub_zero,← ENNReal.ofReal_mul (one_div_pos.mpr (cutoff_pos i)).le]
  simp [(cutoff_pos i).ne']

def law (i : Row) : ProbabilityMeasure (ℝ × ℝ) := by
  letI := conditional_value_probability i
  exact ⟨(LowChernoff.conditionalValueLaw i).map (fun v => (v,bid i v)),
    Measure.isProbabilityMeasure_map (measurable_id.prodMk (measurable_bid i)).aemeasurable⟩

theorem bid_scaled (i : Row) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    bid i (cutoff i*y)=cutoff i*normalizedBid i y := by
  have ht := cutoff_pos i
  by_cases hx : y ≤ x i
  · have hle : cutoff i*y ≤ entry i := by
      unfold entry
      nlinarith
    simp only [bid,if_pos hle,normalizedBid,if_pos hx]
  · have hy0 : 0 < y := (by cases i <;> norm_num [x,xQ] : 0 < x i).trans (lt_of_not_ge hx)
    have hle : ¬ cutoff i*y ≤ entry i := by unfold entry; nlinarith
    rw [bid,if_neg hle,extendedActive_eq i (mul_nonneg ht.le hy.1),normalizedBid,if_neg hx]
    exact ActiveGraphComponent.activeBid_scaled i hy0

def inactiveTolerance (i : Row) (d e : ℝ) : Set (ℝ × ℝ) :=
  {p | (x i-d)*cutoff i ≤ p.1 ∨ |p.2-p.1| ≤ e}

theorem inactiveTolerance_closed (i : Row) (d e : ℝ) : IsClosed (inactiveTolerance i d e) :=
  (isClosed_le continuous_const continuous_fst).union
    (isClosed_le (continuous_snd.sub continuous_fst).abs continuous_const)

theorem inactive_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box (cutoff i) (ReceiptGap.cap i))
    (hi : ∀ d > (0:ℝ),d ≤ x i-1/2 → ∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < e) :
    ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 < entry i → p.2=p.1 := by
  let a := x i-1/2
  have ha : 0 < a := by cases i <;> norm_num [a,x,xQ]
  let d := fun k : ℕ => a/((k:ℝ)+1)
  let e := fun k : ℕ => 1/((k:ℝ)+1)
  have hd (k : ℕ) : 0 < d k := div_pos ha (by positivity)
  have hda (k : ℕ) : d k ≤ x i-1/2 := by
    change a/((k:ℝ)+1) ≤ a
    apply (div_le_iff₀ (by positivity : 0 < (k:ℝ)+1)).mpr
    nlinarith [show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
  have ht (k : ℕ) : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),
      p ∈ box (cutoff i) (ReceiptGap.cap i) ∩ inactiveTolerance i (d k) (e k) := by
    apply limit_supportedOn ((box_compact _ _).inter_right (inactiveTolerance_closed _ _ _)) G G0 hG
    filter_upwards [hi (d k) (hd k) (hda k) (e k) (by dsimp [e]; positivity)] with n hn
    filter_upwards [hbox n,hn] with p hp hpi
    refine ⟨hp,?_⟩
    by_cases h : (x i-d k)*cutoff i ≤ p.1
    · exact Or.inl h
    · exact Or.inr (hpi (lt_of_not_ge h).le).le
  have hdz : Tendsto (fun k => d k*cutoff i) atTop (𝓝 0) := by
    have hh : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [mul_zero,zero_mul] using (tendsto_const_nhds.div_atTop hh).mul_const (cutoff i)
  have hez : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  filter_upwards [ae_all_iff.mpr ht] with p hp hpEntry
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,hkd,hke⟩ := ((hdz.eventually_lt_const (sub_pos.mpr hpEntry)).and
    (hez.eventually_lt_const hε)).exists
  have hcut : p.1 < (x i-d k)*cutoff i := by
    unfold entry at hkd
    nlinarith
  have hsmall := ((hp k).2).resolve_left (not_le_of_gt hcut)
  linarith

theorem law_eq_of_graph (i : Row) (G : Measure (ℝ × ℝ))
    (hv : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hg : ∀ᵐ p ∂G,p.2=bid i p.1) : G=(law i:Measure (ℝ × ℝ)) := by
  have hid : (fun p : ℝ × ℝ => p) =ᵐ[G] (fun p => (p.1,bid i p.1)) :=
    hg.mono fun p hp => Prod.ext rfl hp
  calc
    G=G.map id := by rw [Measure.map_id]
    _=G.map (fun p : ℝ × ℝ => (p.1,bid i p.1)) := Measure.map_congr hid
    _=(G.map Prod.fst).map (fun v => (v,bid i v)) :=
      (Measure.map_map (measurable_id.prodMk (measurable_bid i)) measurable_fst).symm
    _=(law i:Measure (ℝ × ℝ)) := by rw [hv]; rfl

theorem full_limit_eq (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p ∈ box (cutoff i) (ReceiptGap.cap i))
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hinactive : ∀ d > (0:ℝ),d ≤ x i-1/2 → ∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.1 ≤ (x i-d)*cutoff i → |p.2-p.1| < e) :
    G0=law i := by
  have hv := original_marginal_limit i G G0 hG hvalue
  have hb := limit_supportedOn (box_compact _ _) G G0 hG (Eventually.of_forall hbox)
  have ha := active_graph_limit i G G0 hG hbox hactive
  have hi := inactive_limit i G G0 hG hbox hinactive
  have hentry : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),p.1 ≠ entry i := by
    rw [ae_iff]
    simpa only [not_not] using LiteralRankIC.source_value_level_null i (G0:Measure (ℝ × ℝ)) hv (entry i)
  apply Subtype.ext
  apply law_eq_of_graph i (G0:Measure (ℝ × ℝ)) hv
  filter_upwards [hb,ha,hi,hentry] with p hpb hpa hpi hpne
  by_cases hle : p.1 ≤ entry i
  · rw [bid,if_pos hle]
    exact hpi (lt_of_le_of_ne hle hpne)
  · rw [bid,if_neg hle,extendedActive_eq i hpb.1.1]
    exact hpa ⟨lt_of_not_ge hle,hpb.1.2⟩

end FCAppendix.Affine.Uniform06.FullJointLaw
