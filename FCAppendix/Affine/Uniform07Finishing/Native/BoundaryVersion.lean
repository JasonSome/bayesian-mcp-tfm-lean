import FCAppendix.Affine.Uniform07Finishing.Native.LowerVersion
import FCAppendix.Affine.Uniform07Finishing.Native.SourceNativeGame
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def actualBroadcastBestBelow (Γ : FiniteGame m 2 c Seed)
    (R v : ℝ) (a : JointAction 2) : Prop :=
  ∀ i : Fin m, ∀ a' : JointAction 2, a'.routeCount = 2 → a'.bid < R →
    (problem Γ i).payoff v a' ≤ (problem Γ i).payoff v a

def actualLowerBroadcastGood (Γ : FiniteGame m 2 c Seed)
    (U R : ℝ) (z : ℝ × JointAction 2) : Prop :=
  z.2.bid ≤ U ∧ z.2.routeCount = 2 ∧ actualBroadcastBestBelow Γ R z.1 z.2

theorem actual_zero_bid_limit_of_pairwise_comparisons
    (Γ : FiniteGame m 2 c Seed) (U : ℝ) (hg : (Γ).g = 0)
    (i : Fin m) (w v : ℝ) (hw : 0 < w) (hwv : w < v)
    (a : JointAction 2) (haU : a.bid ≤ U) (ha2 : a.routeCount = 2)
    (vn : ℕ → ℝ) (bn : ℕ → Icc (0 : ℝ) U) (b₀ : Icc (0 : ℝ) U)
    (hb₀ : (b₀ : ℝ) = 0) (hvn0 : ∀ n, 0 ≤ vn n)
    (hvn : Tendsto vn atTop (𝓝 v))
    (hbn : Tendsto (fun n => (bn n : ℝ)) atTop (𝓝 0))
    (hwa : ∀ n, (problem Γ i).payoff w (sourceLowerBroadcastAction U (bn n)) ≤
      (problem Γ i).payoff w a)
    (hback : ∀ n, (problem Γ i).payoff (vn n) a ≤
      (problem Γ i).payoff (vn n) (sourceLowerBroadcastAction U (bn n)))
    (a' : JointAction 2)
    (hcomp : ∀ n, (problem Γ i).payoff (vn n) a' ≤
      (problem Γ i).payoff (vn n) (sourceLowerBroadcastAction U (bn n))) :
    (problem Γ i).payoff v a' ≤
      (problem Γ i).payoff v (sourceLowerBroadcastAction U b₀) := by
  let an : ℕ → JointAction 2 := fun n => sourceLowerBroadcastAction U (bn n)
  let Sa := ((problem Γ i).outcome a).success
  let Ca := actualBidPayment Γ i a
  have hCn (n : ℕ) : actualBidPayment Γ i (an n) ≤ 2*(bn n : ℝ) :=
    actualBidPayment_le_two_bid Γ i (an n)
  have hCa0 : Ca = 0 := by
    have hle : ∀ᶠ n in atTop, Ca ≤ 2*(bn n : ℝ) := by
      filter_upwards [hvn.eventually (eventually_gt_nhds hwv)] with n hwn
      have hlow := hwa n
      have hhigh := hback n
      rw [actual_zero_base_payoff Γ hg i w (an n),
        actual_zero_base_payoff Γ hg i w a] at hlow
      rw [actual_zero_base_payoff Γ hg i (vn n) a,
        actual_zero_base_payoff Γ hg i (vn n) (an n)] at hhigh
      change w*((problem Γ i).outcome (an n)).success-actualBidPayment Γ i (an n) ≤ w*Sa-Ca at hlow
      change vn n*Sa-Ca ≤ vn n*((problem Γ i).outcome (an n)).success-actualBidPayment Γ i (an n) at hhigh
      have hsuccess : Sa ≤ ((problem Γ i).outcome (an n)).success := by
        by_contra hn
        have hp := mul_pos (sub_pos.mpr hwn) (sub_pos.mpr (lt_of_not_ge hn))
        nlinarith
      have hnonneg := mul_nonneg hw.le (sub_nonneg.mpr hsuccess)
      exact (show Ca ≤ actualBidPayment Γ i (an n) by nlinarith).trans (hCn n)
    have hz : Ca ≤ 0 := by
      have hh := ge_of_tendsto (hbn.const_mul 2) hle
      simpa only [mul_zero] using hh
    exact le_antisymm hz (actualBidPayment_nonneg Γ i a)
  have hbound : ∀ n, w*(problem Γ i).payoff (vn n) a' ≤
      vn n*(w*Sa+2*(bn n : ℝ)) := by
    intro n
    have hlow := hwa n
    rw [actual_zero_base_payoff Γ hg i w (an n),
      actual_zero_base_payoff Γ hg i w a] at hlow
    change w*((problem Γ i).outcome (an n)).success-actualBidPayment Γ i (an n) ≤ w*Sa-Ca at hlow
    rw [hCa0, sub_zero] at hlow
    have hs : w*((problem Γ i).outcome (an n)).success ≤ w*Sa+2*(bn n : ℝ) := by
      linarith [hCn n]
    have hu := hcomp n
    rw [actual_zero_base_payoff Γ hg i (vn n) (an n)] at hu
    have hu' : (problem Γ i).payoff (vn n) a' ≤
        vn n*((problem Γ i).outcome (an n)).success :=
      hu.trans (sub_le_self _ (actualBidPayment_nonneg Γ i (an n)))
    have hl := mul_le_mul_of_nonneg_left hu' hw.le
    have hr := mul_le_mul_of_nonneg_left hs (hvn0 n)
    nlinarith
  have hleft := ((actual_payoff_continuous_value Γ i a').tendsto v).comp hvn
  have hright : Tendsto (fun n => vn n*(w*Sa+2*(bn n : ℝ))) atTop (𝓝 (v*(w*Sa))) := by
    simpa only [mul_zero, add_zero] using hvn.mul
      ((tendsto_const_nhds (x := w*Sa)).add (hbn.const_mul 2))
  have hlim := le_of_tendsto_of_tendsto (hleft.const_mul w) hright
    (Eventually.of_forall hbound)
  have hu : (problem Γ i).payoff v a' ≤ v*Sa := by nlinarith
  by_cases hab : a.bid = 0
  · have hb : (⟨a.bid, a.bid_nonneg, haU⟩ : Icc (0 : ℝ) U) = b₀ :=
      Subtype.ext (hab.trans hb₀.symm)
    have he : sourceLowerBroadcastAction U b₀ = a := by
      rw [← hb]
      exact sourceLowerBroadcastAction_eq U a haU ha2
    rw [he, actual_zero_base_payoff Γ hg i v a]
    change (problem Γ i).payoff v a' ≤ v*Sa-Ca
    rw [hCa0, sub_zero]
    exact hu
  · have hbpos : 0 < a.bid := lt_of_le_of_ne a.bid_nonneg (Ne.symm hab)
    have hs0 : Sa = 0 := by
      have hh := actualBidPayment_ge_bid_success Γ i a
      change a.bid*Sa ≤ Ca at hh
      rw [hCa0] at hh
      have hs := ((problem Γ i).outcome a).success_nonneg
      dsimp only [Sa] at *
      nlinarith
    rw [hs0, mul_zero] at hu
    apply hu.trans
    rw [actual_zero_base_payoff Γ hg i]
    change 0 ≤ v*((problem Γ i).outcome (sourceLowerBroadcastAction U b₀)).success-
      (b₀ : ℝ)*((problem Γ i).outcome (sourceLowerBroadcastAction U b₀)).charge (Γ).A
    rw [hb₀, zero_mul, sub_zero]
    exact mul_nonneg (hw.trans hwv).le ((problem Γ i).outcome _).success_nonneg

theorem exists_actual_broadcast_anchor (Γ : FiniteGame m 2 c Seed)
    (U R t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hF : (Γ).F = Uniform07.uniformLaw)
    (hcommon : ∀ᵐ z ∂(Γ).F ⊗ₘ (Γ).σ, z.1 ∈ Ioo 0 t → actualLowerBroadcastGood Γ U R z) :
    ∃ w : ℝ, 0 < w ∧ w < t/2 ∧ ∃ a : JointAction 2,
      actualLowerBroadcastGood Γ U R (w,a) := by
  have hcond := Measure.ae_ae_of_ae_compProd hcommon
  have hmass : (Γ).F (Ioo 0 (t/2)) ≠ 0 := by
    rw [hF]
    change (volume.restrict (Icc (0 : ℝ) 1)) (Ioo 0 (t/2)) ≠ 0
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo 0 (t/2) ⊆ Icc (0 : ℝ) 1 from
        fun _ hx => ⟨hx.1.le, by linarith [hx.2]⟩), Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  obtain ⟨w, hw, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass
    (ae_restrict_of_ae hcond)
  obtain ⟨a, haa⟩ := ha.exists
  exact ⟨w, hw.1, hw.2, a, haa ⟨hw.1, by linarith [hw.2]⟩⟩

def actualUpperHalfBroadcastGraph (Γ : FiniteGame m 2 c Seed) (U R t : ℝ) :
    Set (ℝ × Icc (0 : ℝ) U) :=
  {z | t/2 ≤ z.1 ∧ actualBroadcastBestBelow Γ R z.1 (sourceLowerBroadcastAction U z.2)}

theorem actualUpperHalfBroadcastGraph_closed (Γ : FiniteGame m 2 c Seed)
    (U R t : ℝ) (ht : 0 < t) (hUR : U < R) (hg : (Γ).g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (w : ℝ) (hw : 0 < w) (hwt : w < t/2) (a : JointAction 2)
    (ha : actualLowerBroadcastGood Γ U R (w,a)) :
    IsClosed (actualUpperHalfBroadcastGraph Γ U R t) := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hlim
  have hv := (continuous_fst.tendsto z₀).comp hlim
  have hb : Tendsto (fun n => ((z n).2 : ℝ)) atTop (𝓝 (z₀.2 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto z₀).comp hlim
  have hvt : t/2 ≤ z₀.1 := ge_of_tendsto hv (Eventually.of_forall (fun n => (hz n).1))
  refine ⟨hvt, ?_⟩
  intro i a' ha'2 ha'R
  by_cases hb₀ : (z₀.2 : ℝ) = 0
  · apply actual_zero_bid_limit_of_pairwise_comparisons Γ U hg i w z₀.1 hw
      (hwt.trans_le hvt) a ha.1 ha.2.1 (fun n => (z n).1)
      (fun n => (z n).2) z₀.2 hb₀
      (fun n => (half_pos ht).le.trans (hz n).1) hv
    · simpa only [hb₀] using hb
    · exact fun n => ha.2.2 i _ rfl ((z n).2.2.2.trans_lt hUR)
    · exact fun n => (hz n).2 i a ha.2.1 (ha.1.trans_lt hUR)
    · exact fun n => (hz n).2 i a' ha'2 ha'R
  · have hbpos : 0 < (z₀.2 : ℝ) := lt_of_le_of_ne z₀.2.2.1 (Ne.symm hb₀)
    exact le_of_tendsto_of_tendsto
      (((actual_payoff_continuous_value Γ i a').tendsto z₀.1).comp hv)
      ((hpay i z₀ hbpos).tendsto.comp hlim)
      (Eventually.of_forall (fun n => (hz n).2 i a' ha'2 ha'R))

theorem exists_actual_boundary_broadcast_best (Γ : FiniteGame m 2 c Seed)
    (U R t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hUR : U < R)
    (hF : (Γ).F = Uniform07.uniformLaw) (hg : (Γ).g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (hcommon : ∀ᵐ z ∂(Γ).F ⊗ₘ (Γ).σ, z.1 ∈ Ioo 0 t → actualLowerBroadcastGood Γ U R z) :
    ∃ aT : JointAction 2, aT.bid ≤ U ∧ aT.routeCount = 2 ∧
      ∀ i : Fin m, ∀ a' : JointAction 2, a'.routeCount = 2 → a'.bid < R →
        (problem Γ i).payoff t a' ≤ (problem Γ i).payoff t aT := by
  obtain ⟨w, hw, hwt, a, ha⟩ := exists_actual_broadcast_anchor Γ U R t ht ht1 hF hcommon
  let C := actualUpperHalfBroadcastGraph Γ U R t
  let S : Set ℝ := Prod.fst '' C
  have hS : IsClosed S := isClosedMap_fst_of_compactSpace _
    (actualUpperHalfBroadcastGraph_closed Γ U R t ht hUR hg hpay w hw hwt a ha)
  have hcond := Measure.ae_ae_of_ae_compProd hcommon
  have hfull : ∀ᵐ v ∂(Γ).F, v ∈ Ioo (t/2) t → v ∈ S := by
    filter_upwards [hcond] with v hv
    intro hvt
    obtain ⟨a, ha⟩ := hv.exists
    have hg := ha ⟨(half_pos ht).trans hvt.1, hvt.2⟩
    let b : Icc (0 : ℝ) U := ⟨a.bid, a.bid_nonneg, hg.1⟩
    have hab : sourceLowerBroadcastAction U b = a := sourceLowerBroadcastAction_eq U a hg.1 hg.2.1
    refine ⟨(v,b), ⟨hvt.1.le, ?_⟩, rfl⟩
    rw [hab]
    exact hg.2.2
  rw [hF] at hfull
  change ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1), v ∈ Ioo (t/2) t → v ∈ S at hfull
  have hvol : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Ioo (t/2) t → v ∈ S := by
    have hf := (ae_restrict_iff' measurableSet_Icc).mp hfull
    filter_upwards [hf] with v hv
    intro hvt
    exact hv ⟨(half_pos ht).le.trans hvt.1.le, hvt.2.le.trans ht1⟩ hvt
  let O : Set ℝ := Sᶜ ∩ Ioo (t/2) t
  have hO : IsOpen O := hS.isOpen_compl.inter isOpen_Ioo
  have hOae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Oᶜ := by
    filter_upwards [hvol] with v hv
    exact fun h => h.1 (hv h.2)
  have hDense : Dense Oᶜ := Measure.dense_of_ae hOae
  have hAll : Oᶜ = univ := hO.isClosed_compl.closure_eq.symm.trans hDense.closure_eq
  have hInt : Ioo (t/2) t ⊆ S := by
    intro v hv
    by_contra hn
    have hc : v ∈ Oᶜ := by rw [hAll]; trivial
    exact hc ⟨hn,hv⟩
  have htS : t ∈ S := (closure_minimal hInt hS) (by
    rw [closure_Ioo (ne_of_lt (show t/2 < t by linarith))]
    exact ⟨by linarith, le_rfl⟩)
  rcases htS with ⟨⟨v,b⟩, hb, hvt⟩
  change v = t at hvt
  subst v
  exact ⟨sourceLowerBroadcastAction U b, b.2.2, rfl, hb.2⟩

section Source
variable [Nonempty (Fin m)]
  (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
  {R Λ : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
  (hRt : R < Uniform07.cutoff row) (hΛ : 0 < Λ)
  (PL : ProbabilityMeasure (ℝ × JointAction 2))
  (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
    x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
  (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

local notation "Γ" => sourceNativeGame row hc R Λ hΛ PL α hα

include hm hR hRt hLvalue hLroute in

theorem sourceNativeGame_common_broadcast_below
    (hLowerIC : ∀ᵐ z ∂(PL : Measure (ℝ × JointAction 2)),
      actualBroadcastBestBelow Γ R z.1 z.2) :
    ∀ᵐ z ∂(Γ).F ⊗ₘ (Γ).σ, z.1 ∈ Ioo 0 (Uniform07.cutoff row) →
      actualLowerBroadcastGood Γ (Early.bidCap row) R z := by
  rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα,
    sourcePopulation_literal, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [hLroute, hLowerIC] with z hz hi
    exact fun _ => ⟨hz.1,hz.2,hi⟩
  · apply Measure.ae_smul_measure
    filter_upwards [(source_upper_joint_properties row m hm hc hR hRt).2.1] with z hz
    exact fun hv => (not_lt_of_ge hz.1.1 hv.2).elim

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_exists_boundary_broadcast_best
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) (Early.bidCap row), 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) (Early.bidCap row) =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction (Early.bidCap row) z.2)) z)
    (hLowerIC : ∀ᵐ z ∂(PL : Measure (ℝ × JointAction 2)),
      actualBroadcastBestBelow Γ R z.1 z.2) :
    ∃ aT : JointAction 2, aT.bid ≤ Early.bidCap row ∧ aT.routeCount = 2 ∧
      ∀ i : Fin m, ∀ a' : JointAction 2, a'.routeCount = 2 → a'.bid < R →
        (problem Γ i).payoff (Uniform07.cutoff row) a' ≤
          (problem Γ i).payoff (Uniform07.cutoff row) aT :=
  exists_actual_boundary_broadcast_best Γ (Early.bidCap row) R (Uniform07.cutoff row)
    (Uniform07.cutoff_pos row) (Uniform07.cutoff_lt_one row).le hUR rfl rfl hpay
    (sourceNativeGame_common_broadcast_below row hm hc hR hRt hΛ
      PL hLvalue hLroute α hα hLowerIC)

end Source

theorem actual_boundary_utility_eq_of_outcome_invariant
    (Γ : FiniteGame m 2 c Seed) (aT : JointAction 2) (t : ℝ)
    (href : Fin m)
    (hsym : ∀ i : Fin m, (problem Γ i).outcome aT = (problem Γ href).outcome aT) :
    ∀ i : Fin m, (problem Γ i).payoff t aT = (problem Γ href).payoff t aT := by
  intro i
  change ((problem Γ i).outcome aT).utility t aT.bid (Γ).g (Γ).A (Γ).G =
    ((problem Γ href).outcome aT).utility t aT.bid (Γ).g (Γ).A (Γ).G
  rw [hsym i]

end FCAppendix.Affine.Uniform07Finishing
