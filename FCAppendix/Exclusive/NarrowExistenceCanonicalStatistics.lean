import FCAppendix.Exclusive.NarrowExistenceCanonicalGame
import FCAppendix.Exclusive.SourceStationaryAtomless

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

theorem narrowCanonicalGame_active_bids_atomless {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (h : unitInterval) {eps : ℝ}
    (heps : 0 ≤ eps) (heps1 : eps < 1) {H scale : ℝ}
    (hH : 0 < H) (hscale : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta) (hmono : StrictMono beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) :
    NullSingletonClass (submittedBidLawOn
      (narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg)
      (bandHighSet eps H)) := by
  let Gamma := narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg
  let bid := extendedSourceBid eps heps H scale beta
  have hbid : Measurable bid := (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable
  have hpure := measurable_pureAction (d+1) (E := bandHighSet eps H) measurableSet_Icc hbid
  letI : NullSingletonClass (Gamma.F.restrict (bandHighSet eps H)) :=
    narrowPrimitive_restrict_high_atomless h heps1 hH nu
  have hlaw : (Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ =
      (Gamma.F.restrict (bandHighSet eps H)).map
        (fun v => (v,pureAction (d+1) (bandHighSet eps H) bid v)) :=
    Measure.compProd_deterministic hpure
  constructor
  intro z
  have hf : Measurable (fun x : ℝ × JointAction (d+1) => x.2.bid) :=
    (measurable_bid (d+1)).comp measurable_snd
  have hpair : Measurable (fun v => (v,pureAction (d+1) (bandHighSet eps H) bid v)) :=
    measurable_id.prodMk hpure
  change (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
    ((Gamma.F.restrict (bandHighSet eps H)) ⊗ₘ Gamma.σ)) {z}=0
  rw [Measure.map_apply hf (measurableSet_singleton z),hlaw,
    Measure.map_apply hpair (hf (measurableSet_singleton z))]
  change Gamma.F.restrict (bandHighSet eps H)
    {v | (pureAction (d+1) (bandHighSet eps H) bid v).bid=z}=0
  have hinside : ∀ᵐ v ∂Gamma.F.restrict (bandHighSet eps H), v ∈ bandHighSet eps H :=
    ae_restrict_mem measurableSet_Icc
  have he : {v : ℝ | (pureAction (d+1) (bandHighSet eps H) bid v).bid=z} =ᵐ[
      Gamma.F.restrict (bandHighSet eps H)]
      {v : ℝ | (pureAction (d+1) (bandHighSet eps H) bid v).bid=z ∧ v ∈ bandHighSet eps H} := by
    filter_upwards [hinside] with v hv
    change ((pureAction (d+1) (bandHighSet eps H) bid v).bid=z) =
      ((pureAction (d+1) (bandHighSet eps H) bid v).bid=z ∧ v ∈ bandHighSet eps H)
    simp only [hv,and_true]
  rw [measure_congr he]
  apply Set.Subsingleton.measure_zero
  intro v hv w hw
  apply extendedSourceBid_injOn_high heps hH hscale beta hmono hv.2 hw.2
  have hposv : 0 < bid v := extendedSourceBid_pos heps H hscale beta v
  have hposw : 0 < bid w := extendedSourceBid_pos heps H hscale beta w
  have hvbid : (pureAction (d+1) (bandHighSet eps H) bid v).bid=bid v := by
    simp only [pureAction,if_pos hv.2,max_eq_left hposv.le]
  have hwbid : (pureAction (d+1) (bandHighSet eps H) bid w).bid=bid w := by
    simp only [pureAction,if_pos hw.2,max_eq_left hposw.le]
  exact (hvbid.symm.trans hv.1).trans (hw.1.symm.trans hwbid)

theorem narrowCanonicalGame_relative_band {m d c : ℕ}
    (hd : 1 ≤ d) (hc : 0 < c) (h : unitInterval) {eps : ℝ}
    (heps : 0 ≤ eps) (H scale : ℝ) (hs : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g) (eta : ℝ)
    (hlog : ∀ u, Real.exp (beta u) ∈ Ioo (1-eta) (1+eta)) :
    let Gamma := narrowCanonicalGame m d c hd hc h heps H scale beta hbeta nu A G g hg
    ∀ᵐ v ∂Gamma.F, ∀ᵐ a ∂Gamma.σ v, v ∈ bandHighSet eps H →
      a.bid ∈ Ioo (scale*(1-eta)) (scale*(1+eta)) := by
  dsimp only
  apply Eventually.of_forall
  intro v
  change ∀ᵐ a ∂Kernel.deterministic
    (pureAction (d+1) (bandHighSet eps H) (extendedSourceBid eps heps H scale beta))
    (measurable_pureAction (d+1) measurableSet_Icc
      (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable) v, _
  simp only [Kernel.deterministic_apply,ae_dirac_eq,Filter.eventually_pure]
  intro hv
  have hp := extendedSourceBid_pos heps H hs beta v
  have hb : (pureAction (d+1) (bandHighSet eps H)
      (extendedSourceBid eps heps H scale beta) v).bid =
      extendedSourceBid eps heps H scale beta v := by
    simp [pureAction,hv,max_eq_left hp.le]
  rw [hb]
  exact ⟨mul_lt_mul_of_pos_left (hlog _).1 hs,mul_lt_mul_of_pos_left (hlog _).2 hs⟩

end FCAppendix.Bayes.ExclusiveConstruction
