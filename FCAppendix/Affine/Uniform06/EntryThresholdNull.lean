import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.EntryReciprocalLimit
import FCAppendix.Probability.Resample

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryThresholdNull

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual
open scoped BigOperators

theorem raw_lower_singleton (i : Row) (G : Measure (ℝ × ℝ))
    (hnull : ∀ a : ℝ, (G.map Prod.snd) {a}=0) (a : ℝ) :
    (RawMixedSource.source i G) {((0:Fin 4),a)}=0 := by
  have hm : Measurable (fun b : ℝ => ((0:Fin 4),b)) := measurable_const.prodMk measurable_id
  have hpre : (fun b : ℝ => ((0:Fin 4),b)) ⁻¹' {((0:Fin 4),a)}={a} := by
    ext b
    simp
  have hlow : ((G.map Prod.snd).map (fun b : ℝ => ((0:Fin 4),b))) {((0:Fin 4),a)}=0 := by
    rw [Measure.map_apply hm (measurableSet_singleton _),hpre,hnull]
  simp only [RawMixedSource.source,rivalLaw,Measure.add_apply,Measure.smul_apply,
    smul_eq_mul,ENNReal.ofReal_zero,zero_mul,hlow,mul_zero,zero_add]
  simp

theorem raw_lower_bid_ne (i : Row) (G : Measure (ℝ × ℝ))
    (hnull : ∀ a : ℝ, (G.map Prod.snd) {a}=0) (a : ℝ) :
    ∀ᵐ r ∂ RawMixedSource.source i G, r.1=0 → r.2 ≠ a := by
  have hn : ∀ᵐ r ∂ RawMixedSource.source i G, r ≠ ((0:Fin 4),a) := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_eq_eq_singleton] using raw_lower_singleton i G hnull a
  filter_upwards [hn] with r hr htag hbid
  exact hr (Prod.ext htag hbid)

theorem exposure_bid_injective {ξ b x y : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hx : b < x) (hy : b < y)
    (hgx : (1-ξ)*x ≤ b) (hgy : (1-ξ)*y ≤ b)
    (he : exposure ξ b x=exposure ξ b y) : x=y := by
  have hx0 := hb.trans hx
  have hy0 := hb.trans hy
  rw [exposure_of_between hξ hb hx hgx,exposure_of_between hξ hb hy hgy] at he
  have hc := congrArg (fun z : ℝ => z*ξ*x*y) he
  field_simp [hξ.ne',hx0.ne',hy0.ne'] at hc
  have hxy : b*y=b*x := by nlinarith
  exact (mul_left_cancel₀ hb.ne' hxy).symm

theorem ae_injective_exposure_ne (μ : Measure RowRival)
    (hnull : ∀ a : ℝ, ∀ᵐ r ∂μ, r.1=0 → r.2 ≠ a)
    {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (a d : ℝ) :
    ∀ᵐ r ∂μ, r.1=0 → b < r.2 → (1-ξ)*r.2 ≤ b → exposure ξ b r.2+a ≠ d := by
  by_cases hex : ∃ y : ℝ, b< y ∧ (1-ξ)*y≤ b ∧ exposure ξ b y+a=d
  · obtain ⟨y,hy,hgy,hey⟩ := hex
    filter_upwards [hnull y] with r hr htag hbr hgr he
    apply hr htag
    exact exposure_bid_injective hξ hb hbr hy hgr hgy (by linarith)
  · exact ae_of_all _ fun r htag hbr hgr he => hex ⟨r.2,hbr,hgr,he⟩

def contribution {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N))
    (j : Fin N) (r : RowRival) : ℝ :=
  if j ∈ E then 0 else if r.1=0 then exposure ξ b r.2 else 0

def demand {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) (r : Fin N → RowRival) : ℝ :=
  ∑ j, contribution ξ b E j (r j)

lemma measurable_contribution {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) (j : Fin N) :
    Measurable (contribution ξ b E j) := by
  change Measurable (fun r : RowRival => if j ∈ E then 0 else if r.1=0 then exposure ξ b r.2 else 0)
  by_cases hj : j ∈ E
  · simpa only [if_pos hj] using
      (measurable_const : Measurable (fun _ : RowRival => (0:ℝ)))
  · have hm : Measurable (fun r : RowRival => if r.1=0 then exposure ξ b r.2 else 0) := by
      apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      · unfold exposure
        fun_prop
      · exact measurable_const
    simpa only [if_neg hj] using hm

lemma measurable_demand {N : ℕ} (ξ b : ℝ) (E : Finset (Fin N)) :
    Measurable (demand ξ b E) :=
  Finset.measurable_sum _ fun j _ => (measurable_contribution ξ b E j).comp (measurable_pi_apply j)

theorem singled_original_coordinate (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (hnull : ∀ a : ℝ, ∀ᵐ r ∂μ, r.1=0 → r.2 ≠ a)
    {N : ℕ} {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b)
    (E : Finset (Fin N)) (j : Fin N) (hj : j ∉ E) (d : ℝ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => μ),
      (r j).1=0 → b < (r j).2 → (1-ξ)*(r j).2 ≤ b → demand ξ b E r ≠ d := by
  let A := fun r : Fin N → RowRival => ∑ k ∈ Finset.univ.erase j, contribution ξ b E k (r k)
  let P := fun (u : RowRival) (r : Fin N → RowRival) =>
    u.1=0 → b< u.2 → (1-ξ)*u.2≤ b → exposure ξ b u.2+A r ≠ d
  have hAm : Measurable A := Finset.measurable_sum _ fun k _ =>
    (measurable_contribution ξ b E k).comp (measurable_pi_apply k)
  have hPm : MeasurableSet {p : RowRival × (Fin N → RowRival) | P p.1 p.2} := by
    have he : Measurable (fun p : RowRival × (Fin N → RowRival) => exposure ξ b p.1.2+A p.2) := by
      apply Measurable.add _ (hAm.comp measurable_snd)
      unfold exposure
      fun_prop
    have htag : Measurable (fun p : RowRival × (Fin N → RowRival) => p.1.1) := by fun_prop
    have hbid : Measurable (fun p : RowRival × (Fin N → RowRival) => p.1.2) := by fun_prop
    have h1 := measurableSet_eq_fun htag (measurable_const (a := (0:Fin 4)))
    have h2 := measurableSet_lt (measurable_const (a := b)) hbid
    have h3 := measurableSet_le (hbid.const_mul (1-ξ)) (measurable_const (a := b))
    have h4 := (measurableSet_eq_fun he (measurable_const (a := d))).compl
    convert! h1.compl.union (h2.compl.union (h3.compl.union h4)) using 1
    ext p
    simp only [P,mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or,ne_eq]
  have hAi (u : RowRival) (r : Fin N → RowRival) : A (Function.update r j u)=A r := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hPi : ∀ u r u', P u (Function.update r j u') ↔ P u r := by
    intro u r u'
    simp only [P,hAi]
  have hAE : ∀ᵐ u ∂μ, ∀ᵐ r ∂Measure.pi (fun _ : Fin N => μ), P u r := by
    apply (Measure.ae_ae_comm hPm).mpr
    exact ae_of_all _ fun r => ae_injective_exposure_ne μ hnull hξ hb (A r) d
  have hh := FCAppendix.Resample.ae_resample μ j P hPm hPi hAE
  filter_upwards [hh] with r hr htag hbr hgr
  have he : demand ξ b E r=exposure ξ b (r j).2+A r := by
    unfold demand
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [contribution,if_neg hj,if_pos htag]
    rfl
  rw [he]
  exact hr htag hbr hgr

theorem original_fixed_price_threshold_null (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ, (G.map Prod.snd) {a}=0)
    (N : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (E : Finset (Fin N)) (c : ℕ),
      (∃ j, j ∉ E ∧ (r j).1=0 ∧ b<(r j).2 ∧ (1-xi i)*(r j).2≤ b) →
        demand (xi i) b E r ≠ (c:ℝ) := by
  have hall : ∀ (E : Finset (Fin N)) (c : ℕ) (j : Fin N),
      ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
        j ∉ E → (r j).1=0 → b<(r j).2 → (1-xi i)*(r j).2≤ b →
          demand (xi i) b E r ≠ (c:ℝ) := by
    intro E c j
    by_cases hj : j ∈ E
    · exact ae_of_all _ fun _ h => (h hj).elim
    · exact (singled_original_coordinate (RawMixedSource.source i G)
        (raw_lower_bid_ne i G hnull) (xi_pos i) hb E j hj (c:ℝ)).mono fun _ h _ => h
  have he := ae_all_iff.mpr fun E => ae_all_iff.mpr fun c => ae_all_iff.mpr fun j => hall E c j
  filter_upwards [he] with r hr E c hwitness
  obtain ⟨j,hj,htag,hbj,hguard⟩ := hwitness
  exact hr E c j hj htag hbj hguard

theorem original_all_seed_threshold_null (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ, (G.map Prod.snd) {a}=0)
    (N : ℕ) {b : ℝ} (hb : 0 < b) (Seed : Type*)
    (E : (Fin N → RowRival) → Seed → Finset (Fin N))
    (c : (Fin N → RowRival) → Seed → ℕ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G), ∀ u : Seed,
      (∃ j, j ∉ E r u ∧ (r j).1=0 ∧ b<(r j).2 ∧ (1-xi i)*(r j).2≤ b) →
        demand (xi i) b (E r u) r ≠ (c r u:ℝ) := by
  filter_upwards [original_fixed_price_threshold_null i G hnull N hb] with r hr u
  exact hr (E r u) (c r u)

end FCAppendix.Affine.Uniform06.EntryThresholdNull
