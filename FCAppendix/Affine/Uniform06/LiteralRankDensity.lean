import FCAppendix.Affine.Uniform06.LiteralRankAC
import FCAppendix.Affine.Uniform06.SourceSharpDensityConstants

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralRankDensity

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralPrefixContinuity LiteralRankIC LowRankMeasures ICAbsorption
open LiteralWeakRent LiteralLowDuplicate LiteralSuccessLower SourceRankRates
open PureRankCounts PureRankProbability EqualCanonicalRegularity EarlyRankCeiling
open LiteralRankAC LiteralSharpRent LowSuccessComparison SourceSharpDensityConstants
open SharpICAbsorption ScaledMeasure
open FCAppendix.Affine.Uniform07

theorem eventually_source_low_rank_density (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
        (min p.1 (ReceiptGap.cap i))) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (K : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g K → entry i < K → K < RankCutoff.Mstar i →
      K ≤ entry i+cutoff i/400 → extensionEnd i ≤ g.multiplier-g.radius →
      (∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000) →
      (∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
          payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) →
      (bidMeasure i G).restrict (Ioc (0:ℝ) (lowEnd i)) ≪ volume ∧
        ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo (lowEnd i) →
          (lowBidMeasure i G (lowEnd i)).real A ≤ densityConstant i*
            (volume.real A/(1-scaledCoefficient i m*kappa i)+
              (∫ b in A, 1/((m:ℝ)*b))/(1-scaledCoefficient i m)) := by
  filter_upwards [eventually_sharp_absorption_small i,eventually_source_sharp_rank_rent i,
    source_actual_first_pivotal_interval i,eventually_source_low_success_comparable i,
    eventually_ge_atTop (4:ℕ)] with m hsmallSource hrentSource hpiv hcomp hm
  intro G hG hvalue hmenu hatom g K margin hg hK hKM hKfloor hlow hactive hIC
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let H := lowEnd i
  let Z := extensionEnd i
  let μ := lowBidMeasure i G H
  let Γ := lowJointMeasure i G H
  let M := sourceRank (cutoff i) Gb
  let S := sourceS i m G
  let D := sourceD i m G
  let ell := LowChernoff.physicalFloor i
  let cap := localCap i
  have hH : 0 < H := (lowEnd_bounds i).1
  have hHZ : H < Z := (lowEnd_bounds i).2.1
  have hZentry : Z < entry i := by
    have ht := cutoff_pos i
    linarith [(lowEnd_bounds i).2.2.1]
  have hZK : Z ≤ K := (hZentry.trans hK).le
  have hHK : H ≤ K := hHZ.le.trans hZK
  have hgZ : PrefixConditions (xi i) g Z := LowRankMeasures.PrefixConditions.mono hg hZK
  have hgH : PrefixConditions (xi i) g H := LowRankMeasures.PrefixConditions.mono hg hHK
  have hZB : Z ≤ RankCutoff.Mstar i := (lowEnd_bounds i).2.2.2.le
  have hfloor : ∀ᵐ p ∂G, ell p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
  have hnon : ∀ᵐ p ∂G, 0 ≤ p.2 := by
    filter_upwards [hfloor] with p hp
    exact (show 0 ≤ ell p.1 by dsimp [ell]; unfold LowChernoff.physicalFloor; positivity).trans hp
  have hcommon := usedSet_full i m G hvalue hatom g margin (ReceiptGap.cap i) hmenu hIC
  have hexclude := low_bid_values_below_active_start i G hvalue hK
    (lowEnd_bounds i).2.2.1 hactive
  have hK0 : 0 < K := (mul_pos
    (show 0 < x i by cases i <;> norm_num [x,xQ]) (cutoff_pos i)).trans hK
  have hKcap : K ≤ cutoff i := by
    have hr : x i+1/200 < 1 := by cases i <;> norm_num [x,xQ]
    have ht := mul_lt_mul_of_pos_right hr (cutoff_pos i)
    have he : RankCutoff.Mstar i < cutoff i := by
      simpa only [RankCutoff.Mstar,one_mul] using ht
    exact hKM.le.trans he.le
  have hRankCeiling : ∀ b ≤ Z, M b ≤ RankCutoff.Mstar i := by
    have hx : ∀ᵐ p ∂G, p.1 ∈ Ioc K (cutoff i) → Z < p.2 := by
      filter_upwards [hexclude] with p hp hpi
      by_contra hn
      exact not_lt_of_ge hpi.1.le (hp (le_of_not_gt hn))
    intro b hb
    exact (rank_ceiling_of_active_exclusion i G hvalue ⟨hK0.le,hKcap⟩ hx b hb).trans hKM.le
  have hmap : Γ.map Prod.snd=μ := lowJoint_map_snd i G H
  have hΓ := lowJoint_ae i G H hcommon
  have hΓexclude := lowJoint_ae i G H hexclude
  have hrankΓ : ∀ᵐ p ∂Γ, M p.2=p.1 := by
    filter_upwards [hΓ,hΓexclude] with p hp he
    exact source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin (ReceiptGap.cap i)
      hcommon p hp.1 (he.1 (hp.2.2.trans hHZ.le))
  have hcM : Continuous M := continuous_sourceRank (cutoff i) Gb hatom
  have hcell : Continuous ell := LowChernoff.continuous_physicalFloor i
  have hccap : Continuous cap := by unfold cap localCap; fun_prop
  have hcSD := source_extensions_continuous i m G hmenu hatom
  have hIΓ : ∀ᵐ p ∂Γ, ∀ a : ℝ, ell p.1 ≤ a → a ≤ cap p.1 →
      payoff (eta i) p.1 a (S a) (D a) ≤ payoff (eta i) p.1 p.2 (S p.2) (D p.2) := by
    filter_upwards [hΓ] with p hp a ha hcap
    have ha0 : 0 ≤ a := (show 0 ≤ ell p.1 by dsimp [ell]; unfold LowChernoff.physicalFloor; positivity).trans ha
    have haZ : a ≤ Z := hcap.trans (min_le_right _ _)
    have ham : a ∈ Icc (ell p.1) (min p.1 (ReceiptGap.cap i)) :=
      ⟨ha,hcap.trans (min_le_left _ _)⟩
    have hh := hp.1.2.2.2 a ham
    rw [source_extension_payoff i m G g hgZ hlow margin p.1 ⟨ha0,haZ⟩,
      source_extension_payoff i m G g hgZ hlow margin p.1 ⟨hp.2.1.le,hp.2.2.trans hHZ.le⟩] at hh
    exact hh
  have hIμ := rank_IC_pushforward Γ Prod.fst Prod.snd measurable_snd μ hmap M ell cap S D (eta i)
    hcM hcell hccap hcSD.1 hcSD.2 hrankΓ hIΓ
  have hfloorμ : ∀ᵐ b ∂μ, ell (M b) ≤ b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (hcell.measurable.comp hcM.measurable) measurable_id)).mpr
    filter_upwards [hΓ,hrankΓ] with p hp hr
    change ell (M p.2) ≤ p.2
    rw [hr]
    exact hp.1.2.2.1.1
  let r := rentConstant i
  let Q : ℝ → ℝ := fun b => pureRank (m-1) (capacity m) ((1+cutoff i)/2) (M b)
  have hr : 0 < r := rentConstant_pos i
  have hrentΓ : ∀ᵐ p ∂Γ, r*min p.1 (1/(m:ℝ)) ≤ p.1-p.2 := by
    filter_upwards [hΓ,hΓexclude] with p hp he
    exact hrentSource G inferInstance hvalue hatom g K (ReceiptGap.cap i) margin
      hg hKfloor hKM.le hlow hcommon p hp.1
      (he.1 (hp.2.2.trans hHZ.le)) (hp.2.2.trans hHZ.le)
  have hrentμ : ∀ᵐ b ∂μ, r*min (M b) (1/(m:ℝ)) ≤ M b-b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (by fun_prop) (hcM.measurable.sub measurable_id))).mpr
    filter_upwards [hrentΓ,hrankΓ] with p hp hpR
    change r*min (M p.2) (1/(m:ℝ)) ≤ M p.2-p.2
    rw [hpR]
    exact hp
  have hbidμ : ∀ᵐ b ∂μ, b ≤ M b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le measurable_id hcM.measurable)).mpr
    filter_upwards [hΓ,hrankΓ] with p hp hpR
    rw [hpR]
    exact hp.1.2.2.1.2.trans (min_le_left _ _)
  have hrentClosed := continuous_le_on_closed_support μ
    (fun b => r*min (M b) (1/(m:ℝ))) (fun b => M b-b)
    (by fun_prop) (hcM.sub continuous_id) hrentμ
  have hbidClosed := continuous_le_on_closed_support μ id M continuous_id hcM hbidμ
  have hrent : ∀ a ∈ μ.support, a ∈ Ioc 0 H → r*min a (1/(m:ℝ)) ≤ M a-a := by
    intro a ha _
    exact (mul_le_mul_of_nonneg_left
      (min_le_min_right _ (hbidClosed a ha)) hr.le).trans (hrentClosed a ha)
  obtain ⟨δ,hδ,hfirstSource⟩ := hpiv G inferInstance hnon hatom g H margin hgH
    (fun b hb => hRankCeiling b (hb.2.trans hHZ.le))
  have hdupSource := (source_actual_duplicate_level_and_interval i G hvalue hfloor hatom hm
    g hgH (hHZ.le.trans hlow) (hHZ.le.trans hZB) hHZ.le margin).2
  let B : ℝ := ((m-1:ℕ):ℝ)*pureRare m
  let L : ℝ := 2*equalRare i m/xi i
  have hLm : 0 < Lm i m := (Lm_mem_Ioc i hm).1
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hη : eta i ∈ Icc (0:ℝ) 1 := by cases i <;> norm_num [eta,etaQ]
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i < 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hB0 : 0 ≤ B := by dsimp [B,pureRare]; positivity
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact div_nonneg (mul_nonneg (by norm_num) (by unfold equalRare; positivity)) (xi_pos i).le
  have hsmall : 8*80000*B < r*Lm i m := by
    dsimp only [B,r]
    nlinarith [hsmallSource.2.2.1]
  have hLsmall : L ≤ Lm i m := hsmallSource.2.2.2
  have hagree {b : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
      sourceSuccess i m G g margin b=S b ∧ sourceDuplicate i m G g margin b=D b :=
    source_extensions_agree i m G g hgZ hlow margin hb (hbH.trans hHZ.le)
  have hQ : ∀ a ∈ Ioc 0 H, Lm i m ≤ Q a := by
    intro a _
    exact unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) Gb a (m-1) (capacity m)
  have hQmono : Monotone Q := source_rank_kernel_monotone (cutoff_mem i) Gb (m-1) (capacity m)
  have hfirst : ∀ a b : ℝ, 0 < a → a < b → b ≤ H → b-a ≤ δ →
      ((m:ℝ)/80000)*Q a*μ.real (Ioc a b) ≤ S b-S a := by
    intro a b ha hab hb hstep
    have hh := hfirstSource a b ha hab hb hstep
    rw [(hagree (ha.trans hab) hb).1,(hagree ha (hab.le.trans hb)).1] at hh
    rw [lowBidMeasure_real_Ioc i G ha.le hb]
    have hmass : 0 ≤ cutoff i*Gb.real (Ioc a b) := mul_nonneg (cutoff_pos i).le measureReal_nonneg
    have hq := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hQmono hab.le) (show 0 ≤ (m:ℝ)/80000 by positivity)) hmass
    exact hq.trans hh
  have hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ H →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (kappa i*a) (kappa i*b)))+L*(b-a)/a := by
    intro a b ha hab hb
    have hh := hdupSource a b ha hab hb
    rw [(hagree (ha.trans hab) hb).2,(hagree ha (hab.le.trans hb)).2] at hh
    have hkb : kappa i*b ≤ H := (mul_le_of_le_one_left (ha.trans hab).le hκ1.le).trans hb
    rw [lowBidMeasure_real_Ioc i G ha.le hb,
      lowBidMeasure_real_Ioc i G (mul_nonneg hκ.le ha.le) hkb]
    convert! hh using 1
    dsimp only [B,L]
    field_simp [(xi_pos i).ne',ha.ne']
  have hlevel : ∀ a ∈ Ioc 0 H, S a+eta i*D a ≤ 4*Q a := by
    intro a ha
    have hh := (hcomp G inferInstance hvalue hfloor hatom g H margin hgH
      (hHZ.le.trans hlow) hHZ.le a ha.1 ha.2 (hRankCeiling a (ha.2.trans hHZ.le))).2.2
    rw [(hagree ha.1 ha.2).1,(hagree ha.1 ha.2).2] at hh
    exact hh
  have hcapLegal : ∀ v b : ℝ, b < v → b ≤ H → b < cap v := by
    intro v b hbv hbH
    exact lt_min (lt_min hbv (hbH.trans_lt (lowEnd_below_cap i))) (hbH.trans_lt hHZ)
  have hH1 : H ≤ 1 := by dsimp [H,lowEnd]; linarith [cutoff_lt_one i,cutoff_pos i]
  have hBorel' := sharp_IC_weighted_Borel μ (lowBidMeasure_atomless i G hatom H)
    M ell cap S D Q (eta i) (kappa i) r 80000 (m:ℝ) (Lm i m) B L H δ
    hcM hcell hccap hcSD.1 hcSD.2 hIμ hfloorμ hcapLegal hη hκ hr (by norm_num)
    hmR hLm hB0 hL0 hsmall hLsmall hH1 hδ hQ hrent hlevel hfirst hdup
  have hBorel : ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo H →
      μ.real A ≤ densityConstant i*(∫ b in A, rentWeight (m:ℝ) b)+
        scaledCoefficient i m*μ.real (scaledSet (kappa i) A) := by
    intro lo hlo A hAm hA
    have hh := hBorel' lo hlo A hAm hA
    convert! hh using 1
    dsimp only [densityConstant,scaledCoefficient,B,r]
    ring
  have hres := sharp_IC_integrated_density μ hκ hκ1.le hsmallSource.1 hsmallSource.2.1
    (densityConstant_pos i).le (show 0 < (m:ℝ) by linarith) hBorel
  refine ⟨?_,hres.2⟩
  simpa only [μ,lowBidMeasure,Measure.restrict_restrict measurableSet_Ioc,inter_self] using hres.1

end FCAppendix.Affine.Uniform06.LiteralRankDensity
