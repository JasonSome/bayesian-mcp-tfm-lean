import FCAppendix.Exclusive.SourceStationaryGame

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

theorem extendedSourceBid_strictMonoOn_high {eps H scale : ℝ} (heps : 0 ≤ eps) (hH : 0 < H)
    (hscale : 0 < scale) (beta : ValueBand eps → ℝ) (hmono : StrictMono beta) :
    StrictMonoOn (extendedSourceBid eps heps H scale beta) (bandHighSet eps H) := by
  intro v hv w hw hvw
  let u := normalizedType eps heps (v/H)
  let z := normalizedType eps heps (w/H)
  have hv' : H*(u : ℝ)=v := highValue_normalization heps hH hv
  have hw' : H*(z : ℝ)=w := highValue_normalization heps hH hw
  have huz : u<z := by
    change (u : ℝ)<(z : ℝ)
    nlinarith
  have hh := extendedSourceBid_high_strictMono heps hH.ne' hscale beta hmono huz
  simpa only [hv',hw'] using hh

theorem extendedSourceBid_injOn_high {eps H scale : ℝ} (heps : 0 ≤ eps) (hH : 0 < H)
    (hscale : 0 < scale) (beta : ValueBand eps → ℝ) (hmono : StrictMono beta) :
    Set.InjOn (extendedSourceBid eps heps H scale beta) (bandHighSet eps H) := by
  intro v hv w hw he
  let u := normalizedType eps heps (v/H)
  let z := normalizedType eps heps (w/H)
  have hv' : H*(u : ℝ)=v := highValue_normalization heps hH hv
  have hw' : H*(z : ℝ)=w := highValue_normalization heps hH hw
  have hbid : scale*Real.exp (beta u)=scale*Real.exp (beta z) := by
    rw [← extendedSourceBid_high heps hH.ne' scale beta u,
      ← extendedSourceBid_high heps hH.ne' scale beta z,hv',hw']
    exact he
  have huz : u=z := hmono.injective (Real.exp_injective (mul_left_cancel₀ hscale.ne' hbid))
  rw [← hv',← hw',huz]

def submittedBidLawOn {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m n c Seed) (E : Set ℝ) : Measure ℝ :=
  (((Gamma.F.restrict E) ⊗ₘ Gamma.σ).map (fun x => x.2.bid))

theorem bandSourceGame_active_bids_atomless {m n c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) {H scale : ℝ}
    (hH : 0 < H) (hscale : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta) (hmono : StrictMono beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) {L : ℝ} (hL : 0 < L) (cutoff : ℝ) :
    NullSingletonClass (submittedBidLawOn
      (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff)
      (bandHighSet eps H)) := by
  let Gamma := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
  let bid := extendedSourceBid eps heps H scale beta
  have hbid : Measurable bid := (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable
  have hpure := measurable_pureAction n (E := bandHighSet eps H) measurableSet_Icc hbid
  letI : NullSingletonClass Gamma.F := by
    change NullSingletonClass (bandPrimitive h H nu g L)
    exact bandPrimitive_atomless h nu g hH hL
  have hlaw : (Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ =
      (Gamma.F.restrict (bandHighSet eps H)).map (fun v => (v,pureAction n (bandHighSet eps H) bid v)) :=
    Measure.compProd_deterministic hpure
  constructor
  intro z
  have hf : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hpair : Measurable (fun v => (v,pureAction n (bandHighSet eps H) bid v)) :=
    measurable_id.prodMk hpure
  change (Measure.map (fun x : ℝ × JointAction n => x.2.bid)
    ((Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ)) {z}=0
  rw [Measure.map_apply hf (measurableSet_singleton z),hlaw,
    Measure.map_apply hpair (hf (measurableSet_singleton z))]
  change Gamma.F.restrict (bandHighSet eps H)
    {v | (pureAction n (bandHighSet eps H) bid v).bid=z}=0
  have hactbid : Measurable (fun v => (pureAction n (bandHighSet eps H) bid v).bid) :=
    (measurable_bid n).comp hpure
  have hset : MeasurableSet {v | (pureAction n (bandHighSet eps H) bid v).bid=z} :=
    measurableSet_eq_fun hactbid measurable_const
  rw [Measure.restrict_apply hset]
  apply Set.Subsingleton.measure_zero
  intro v hv w hw
  apply extendedSourceBid_injOn_high heps hH hscale beta hmono hv.2 hw.2
  have hposv : 0 < bid v := extendedSourceBid_pos heps H hscale beta v
  have hposw : 0 < bid w := extendedSourceBid_pos heps H hscale beta w
  have hvbid : (pureAction n (bandHighSet eps H) bid v).bid=bid v := by
    simp only [pureAction,if_pos hv.2,max_eq_left hposv.le]
  have hwbid : (pureAction n (bandHighSet eps H) bid w).bid=bid w := by
    simp only [pureAction,if_pos hw.2,max_eq_left hposw.le]
  exact (hvbid.symm.trans hv.1).trans (hw.1.symm.trans hwbid)

theorem bandSourceGame_active_bid_singleton_zero {m n c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) {H scale : ℝ}
    (hH : 0 < H) (hscale : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta) (hmono : StrictMono beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) {L : ℝ} (hL : 0 < L) (cutoff z : ℝ) :
    let Gamma := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
    ((Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ) {x | x.2.bid=z}=0 := by
  let Gamma := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
  letI := bandSourceGame_active_bids_atomless hm hn hc h heps hH hscale beta hbeta hmono
    nu A G g hg hL cutoff
  have hz := measure_singleton (μ := submittedBidLawOn Gamma (bandHighSet eps H)) z
  have hf : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  rw [submittedBidLawOn,Measure.map_apply hf (measurableSet_singleton z)] at hz
  change ((Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ)
    ((fun x : ℝ × JointAction n => x.2.bid) ⁻¹' {z})=0
  exact hz

end FCAppendix.Bayes.ExclusiveConstruction
