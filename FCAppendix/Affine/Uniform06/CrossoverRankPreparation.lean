import FCAppendix.Affine.Uniform06.PositivePrefixRegularity
import FCAppendix.Affine.Uniform06.LowRankMeasures

noncomputable section
namespace FCAppendix.Affine.Uniform06.CrossoverRankPreparation

open MeasureTheory Set Filter Topology
open ICAbsorption Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralPureComponents LiteralRankIC LowRankMeasures LiteralWeakRent LiteralLowDuplicate
open LiteralSuccessLower SourceRankRates PureRankCounts PureRankProbability
open EqualCanonicalRegularity EarlyRankCeiling CanonicalPrefixLipschitz PositivePrefixRegularity
open FCAppendix.Affine.Uniform07

def S (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (Z : ℝ) : ℝ → ℝ :=
  fullSuccessExtension (cutoff i) (xi i) (G.map Prod.snd) (capacity m) (m-1) g margin Z

def D (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (Z : ℝ) : ℝ → ℝ :=
  fullDuplicateExtension (cutoff i) (xi i) (G.map Prod.snd) (capacity m) (m-1) g margin Z

def cap (i : Row) (Z v : ℝ) : ℝ := min (min v (ReceiptGap.cap i)) Z

theorem source_extensions_agree (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {Z : ℝ} (hg : PrefixConditions (xi i) g Z)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbZ : b ≤ Z) :
    sourceSuccess i m G g margin b=S i m G g margin Z b ∧
      sourceDuplicate i m G g margin b=D i m G g margin Z b := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  simpa only [S,D,sourceSuccess,sourceDuplicate,source_kappa i] using
    full_extensions_agree (cutoff_mem i) (xi_pos i)
      (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
      (show 1-2*xi i ≠ 0 by rw [← source_eta i]; exact (eta_pos i).ne')
      (G.map Prod.snd) (capacity m) (m-1) g hg margin hb hbZ

theorem source_extension_payoff (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {Z : ℝ} (hg : PrefixConditions (xi i) g Z)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (w : ℝ) {b : ℝ}
    (hb : b ∈ Icc (0:ℝ) Z) :
    payoff (eta i) w b (sourceSuccess i m G g margin b) (sourceDuplicate i m G g margin b)=
      payoff (eta i) w b (S i m G g margin Z b) (D i m G g margin Z b) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  simpa only [S,D,sourceSuccess,sourceDuplicate,source_kappa i,source_eta i] using
    full_extension_payoff (cutoff_mem i) (xi_pos i)
      (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
      (show 1-2*xi i ≠ 0 by rw [← source_eta i]; exact (eta_pos i).ne')
      (G.map Prod.snd) (capacity m) (m-1) g hg margin w hb

theorem source_extensions_continuous (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
      (min p.1 (ReceiptGap.cap i)))
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {Z : ℝ} (hZ : 0 < Z) (hg : PrefixConditions (xi i) g Z)
    (margin : (Fin (m-1) → Fin 4) → ℝ) :
    ContinuousOn (S i m G g margin Z) (Ioi 0) ∧
      ContinuousOn (D i m G g margin Z) (Ioi 0) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact full_extensions_continuous (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show 1-2*xi i ≠ 0 by rw [← source_eta i]; exact (eta_pos i).ne')
    (ReceiptGap.cap_bounds i).1.le hZ (G.map Prod.snd)
    (source_bid_support i G hmenu) hatom (capacity m) (m-1) g hg margin

theorem active_exclusion (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {K Z err : ℝ} (hK : 0 < K)
    (hgap : Z+err < ActiveGraphComponent.activeBid i K)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ err) :
    ∀ᵐ p ∂G, p.2 ≤ Z → p.1 < K := by
  filter_upwards [same_joint_value_support i G hvalue,hactive] with p hp ha hpb
  by_contra hn
  have hKp : K ≤ p.1 := le_of_not_gt hn
  have hm := activeBid_monotone_positive i hK (hK.trans_le hKp) hKp
  have hd := (abs_le.mp (ha ⟨hKp,hp.2⟩)).1
  linarith

theorem half_value_weak_rent {η L v b U : ℝ} {s d : ℝ → ℝ}
    (hη : η ∈ Icc (0:ℝ) 1) (hL : L ∈ Ioc (0:ℝ) 1)
    (hb : 0 < b) (hmenu : b ∈ Icc (0:ℝ) (min v U))
    (hSused : s b ≤ 1) (hDused : 0 ≤ d b)
    (hSbench : L ≤ s (v/2)) (hDbench : d (v/2) ∈ Icc (0:ℝ) (L/10))
    (hIC : ∀ a ∈ Icc (0:ℝ) (min v U),
      payoff η v a (s a) (d a) ≤ payoff η v b (s b) (d b)) :
    (L/10)*b ≤ v-b := by
  have hbv : b ≤ v := hmenu.2.trans (min_le_left _ _)
  have hv : 0 < v := hb.trans_le hbv
  by_cases hhalf : b ≤ v/2
  · have hh := mul_le_mul_of_nonneg_right hL.2 hb.le
    nlinarith
  have ha : v/2 ∈ Icc (0:ℝ) (min v U) :=
    ⟨(half_pos hv).le,(le_of_lt (lt_of_not_ge hhalf)).trans hmenu.2⟩
  have hic := hIC (v/2) ha
  have hgain := mul_le_mul_of_nonneg_left hSbench (half_pos hv).le
  have hcost := mul_le_mul_of_nonneg_left hDbench.2 (half_pos hv).le
  have hcostη := mul_le_mul_of_nonneg_right hη.2
    (mul_nonneg (half_pos hv).le hDbench.1)
  have hused := mul_le_mul_of_nonneg_left hSused (sub_nonneg.mpr hbv)
  have husedD := mul_nonneg (mul_nonneg hη.1 hb.le) hDused
  have hbL := mul_le_mul_of_nonneg_left hbv hL.1.le
  unfold payoff at hic
  nlinarith

theorem source_used_weak_rent (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (hrare : pureRare m+equalRare i m ≤ Lm i m/10)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (hK : entry i < K) (hKfloor : K ≤ entry i+cutoff i/400)
    (hlow : extensionEnd i ≤ g.multiplier-g.radius)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ)
    (p : ℝ × ℝ) (hp : p ∈ usedSet i m G g margin U) (hpK : p.1 < K) :
    (Lm i m/10)*p.2 ≤ p.1-p.2 := by
  have ht := cutoff_pos i
  have hKcap : K < cutoff i := by
    have hc : x i+1/400 < 1 := by cases i <;> norm_num [x,xQ]
    have hh := mul_lt_mul_of_pos_right hc ht
    unfold entry at hKfloor
    linarith
  have hZentry : extensionEnd i < entry i := by
    have hc : (501/1000:ℝ) < x i := by cases i <;> norm_num [x,xQ]
    simpa only [extensionEnd,entry] using mul_lt_mul_of_pos_right hc ht
  have hgZ := LowRankMeasures.PrefixConditions.mono hg (hZentry.trans hK).le
  have hzero := source_floor_zero (hpK.le.trans hKfloor)
  have hv : 0 < p.1 := hp.2.1.trans_le (hp.2.2.1.2.trans (min_le_left _ _))
  have ha : 0 < p.1/2 := half_pos hv
  have haZ : p.1/2 ≤ extensionEnd i := by
    have hh := hpK.trans hKcap
    unfold extensionEnd
    linarith
  have hDa := (source_actual_duplicate_level_and_interval i G hvalue hfloor hatom hm
    g hgZ hlow (lowEnd_bounds i).2.2.2.le le_rfl margin).1 (p.1/2) ha haZ
  have hbounds := source_first_duplicate_bounds i m G g margin p.2
  have hbench := source_first_duplicate_bounds i m G g margin (p.1/2)
  apply half_value_weak_rent
    (show eta i ∈ Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ])
    (Lm_mem_Ioc i hm) hp.2.1
    (by simpa only [hzero] using hp.2.2.1) hbounds.1.2 hbounds.2.1
    (source_actual_success_ge_Lm i hm G g hgZ margin ha haZ (hatom _))
    ⟨hbench.2.1,hDa.trans hrare⟩
  intro a ha
  exact hp.2.2.2 a (by simpa only [hzero] using ha)

variable (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (H Z K : ℝ)

structure Prepared : Prop where
  rank_continuous : Continuous (sourceRank (cutoff i) (G.map Prod.snd))
  kernel_continuous : ContinuousOn (S i m G g margin Z) (Ioi 0) ∧
    ContinuousOn (D i m G g margin Z) (Ioi 0)
  rank_le : ∀ b ≤ Z, sourceRank (cutoff i) (G.map Prod.snd) b ≤ K
  rank_IC : ∀ᵐ b ∂lowBidMeasure i G H, 0 < b → ∀ a : ℝ, 0 < a →
    LowChernoff.physicalFloor i (sourceRank (cutoff i) (G.map Prod.snd) b) < a →
    a < cap i Z (sourceRank (cutoff i) (G.map Prod.snd) b) →
    payoff (eta i) (sourceRank (cutoff i) (G.map Prod.snd) b) a
      (S i m G g margin Z a) (D i m G g margin Z a) ≤
    payoff (eta i) (sourceRank (cutoff i) (G.map Prod.snd) b) b
      (S i m G g margin Z b) (D i m G g margin Z b)
  floor_on_rank : ∀ᵐ b ∂lowBidMeasure i G H,
    LowChernoff.physicalFloor i (sourceRank (cutoff i) (G.map Prod.snd) b) ≤ b
  rent_on_support : ∀ b ∈ (lowBidMeasure i G H).support,
    (Lm i m/10)*b ≤ sourceRank (cutoff i) (G.map Prod.snd) b-b

variable {i m G g margin H Z K}

theorem prepare_source (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (hrare : pureRare m+equalRare i m ≤ Lm i m/10)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
      (min p.1 (ReceiptGap.cap i)))
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {H Z K err : ℝ}
    (hH : 0 < H) (hHZ : H < Z) (hZK : Z ≤ K)
    (hK : entry i < K) (hKfloor : K ≤ entry i+cutoff i/400)
    (hg : PrefixConditions (xi i) g K)
    (hlow : extensionEnd i ≤ g.multiplier-g.radius)
    (hgap : Z+err < ActiveGraphComponent.activeBid i K)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ err)
    (margin : (Fin (m-1) → Fin 4) → ℝ)
    (hIC : ∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
      payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
        payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) :
    Prepared i m G g margin H Z K := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := lowBidMeasure i G H
  let Γ := lowJointMeasure i G H
  let M := sourceRank (cutoff i) Gb
  let s := S i m G g margin Z
  let d := D i m G g margin Z
  let ell := LowChernoff.physicalFloor i
  let cp := cap i Z
  have hZ : 0 < Z := hH.trans hHZ
  have hgZ := LowRankMeasures.PrefixConditions.mono hg hZK
  have hK0 : 0 < K := hZ.trans_le hZK
  have hKcap : K ≤ cutoff i := by
    have hc : x i+1/400 < 1 := by cases i <;> norm_num [x,xQ]
    have hh := mul_lt_mul_of_pos_right hc (cutoff_pos i)
    unfold entry at hKfloor
    linarith
  have hfloor : ∀ᵐ p ∂G, ell p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
  have hcommon := usedSet_full i m G hvalue hatom g margin (ReceiptGap.cap i) hmenu hIC
  have hexclude := active_exclusion i G hvalue hK0 hgap hactive
  have hRankK : ∀ b ≤ Z, M b ≤ K := by
    have hx : ∀ᵐ p ∂G, p.1 ∈ Ioc K (cutoff i) → Z < p.2 := by
      filter_upwards [hexclude] with p hp hpi
      by_contra hn
      exact not_lt_of_ge hpi.1.le (hp (le_of_not_gt hn))
    intro b hb
    exact rank_ceiling_of_active_exclusion i G hvalue ⟨hK0.le,hKcap⟩ hx b hb
  have hmap : Γ.map Prod.snd=μ := lowJoint_map_snd i G H
  have hΓ := lowJoint_ae i G H hcommon
  have hΓexclude := lowJoint_ae i G H hexclude
  have hrankΓ : ∀ᵐ p ∂Γ, M p.2=p.1 := by
    filter_upwards [hΓ,hΓexclude] with p hp he
    exact source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin (ReceiptGap.cap i)
      hcommon p hp.1 (he.1 (hp.2.2.trans hHZ.le))
  have hcM : Continuous M := continuous_sourceRank (cutoff i) Gb hatom
  have hcell : Continuous ell := LowChernoff.continuous_physicalFloor i
  have hccap : Continuous cp := by unfold cp cap; fun_prop
  have hcSD := source_extensions_continuous i m G hmenu hatom g hZ hgZ margin
  have hIΓ : ∀ᵐ p ∂Γ, ∀ a : ℝ, ell p.1 ≤ a → a ≤ cp p.1 →
      payoff (eta i) p.1 a (s a) (d a) ≤ payoff (eta i) p.1 p.2 (s p.2) (d p.2) := by
    filter_upwards [hΓ] with p hp a ha hcap
    have ha0 : 0 ≤ a := (show 0 ≤ ell p.1 by dsimp [ell]; unfold LowChernoff.physicalFloor; positivity).trans ha
    have haZ : a ≤ Z := hcap.trans (min_le_right _ _)
    have ham : a ∈ Icc (ell p.1) (min p.1 (ReceiptGap.cap i)) :=
      ⟨ha,hcap.trans (min_le_left _ _)⟩
    have hh := hp.1.2.2.2 a ham
    rw [source_extension_payoff i m G g hgZ margin p.1 ⟨ha0,haZ⟩,
      source_extension_payoff i m G g hgZ margin p.1 ⟨hp.2.1.le,hp.2.2.trans hHZ.le⟩] at hh
    exact hh
  have hIμ := rank_IC_pushforward Γ Prod.fst Prod.snd measurable_snd μ hmap M ell cp s d (eta i)
    hcM hcell hccap hcSD.1 hcSD.2 hrankΓ hIΓ
  have hfloorμ : ∀ᵐ b ∂μ, ell (M b) ≤ b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (hcell.measurable.comp hcM.measurable) measurable_id)).mpr
    filter_upwards [hΓ,hrankΓ] with p hp hr
    change ell (M p.2) ≤ p.2
    rw [hr]
    exact hp.1.2.2.1.1
  have hrentΓ : ∀ᵐ p ∂Γ, (Lm i m/10)*p.2 ≤ p.1-p.2 := by
    filter_upwards [hΓ,hΓexclude] with p hp he
    exact source_used_weak_rent i hm hrare G hvalue hfloor hatom g hg hK hKfloor hlow
      margin (ReceiptGap.cap i) p hp.1 (he.1 (hp.2.2.trans hHZ.le))
  have hrentμ : ∀ᵐ b ∂μ, (Lm i m/10)*b ≤ M b-b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (by fun_prop) (hcM.measurable.sub measurable_id))).mpr
    filter_upwards [hrentΓ,hrankΓ] with p hp hr
    change (Lm i m/10)*p.2 ≤ M p.2-p.2
    rw [hr]
    exact hp
  exact ⟨hcM,hcSD,hRankK,hIμ,hfloorμ,
    continuous_le_on_closed_support μ (fun b => (Lm i m/10)*b) (fun b => M b-b)
      (by fun_prop) (hcM.sub continuous_id) hrentμ⟩

end FCAppendix.Affine.Uniform06.CrossoverRankPreparation
