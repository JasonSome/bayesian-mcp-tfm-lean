import FCAppendix.Affine.Uniform06.RankDensityRepresentative
import FCAppendix.Affine.Uniform06.SupportedStieltjesIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralStieltjesIC

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralPrefixContinuity LiteralRankIC LowRankMeasures LiteralRankAC
open LiteralWeakRent LiteralLowDuplicate LiteralSuccessLower SourceRankRates
open PureRankCounts PureRankProbability EqualCanonicalRegularity EarlyRankCeiling
open LiteralRankDensity RankDensityRepresentative SourceSharpDensityConstants
open ScaledMeasure CompactStieltjes SupportedStieltjesIC
open FCAppendix.Affine.Uniform07

theorem compact_rank_interval_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {κ ε C m H lo : ℝ} (hm : 0 < m) (hlo : 0 < lo)
    (hC : 0 ≤ C) (hε : ε < 1) (_hεκ : ε*κ < 1)
    (hbound : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a H →
      μ.real A ≤ C*(volume.real A/(1-ε*κ)+(∫ b in A, 1/(m*b))/(1-ε)))
    {a b : ℝ} (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ H) :
    μ.real (Ioc a b) ≤ geometricBound κ ε C m lo*(b-a) := by
  have hsub : Ioc a b ⊆ Icc lo H := fun x hx =>
    ⟨ha.trans hx.1.le,hx.2.trans hb⟩
  letI : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    ⟨by simp only [Measure.restrict_apply_univ,Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hrec : (∫ x in Ioc a b, 1/(m*x)) ≤ (b-a)/(m*lo) := by
    have hf := reciprocal_integrableOn hm hlo hsub
    have hh := integral_mono_ae hf (integrable_const (1/(m*lo))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hm hlo)
        (mul_le_mul_of_nonneg_left (ha.trans hx.1.le) hm.le))
    have hc : (∫ _x in Ioc a b, (1/(m*lo):ℝ))=(b-a)/(m*lo) := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab),smul_eq_mul]
      ring
    rwa [hc] at hh
  have hvol : volume.real (Ioc a b)=b-a := by
    rw [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hh := (hbound lo hlo (Ioc a b) measurableSet_Ioc hsub).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_right hrec (sub_nonneg.mpr hε.le))) hC)
  rw [hvol] at hh
  convert! hh using 1
  unfold geometricBound
  ring

theorem duplicate_increment_of_compact_rank
    (μ : Measure ℝ) [IsFiniteMeasure μ] (D : ℝ → ℝ)
    {κ ε C m H lo B L : ℝ} (hm : 0 < m) (hlo : 0 < lo)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hC : 0 ≤ C) (hε : ε < 1) (hεκ : ε*κ < 1)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a H →
      μ.real A ≤ C*(volume.real A/(1-ε*κ)+(∫ b in A, 1/(m*b))/(1-ε)))
    (hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ H →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (κ*a) (κ*b)))+L*(b-a)/a) :
    ∀ a ∈ Icc lo H, ∀ b ∈ Icc lo H, a ≤ b →
      D b-D a ≤
        (B*(geometricBound κ ε C m lo+κ*geometricBound κ ε C m (κ*lo))+L/lo)*(b-a) := by
  intro a ha b hb hab
  by_cases he : a=b
  · subst b
    simp
  have hab' : a < b := lt_of_le_of_ne hab he
  have ha0 : 0 < a := hlo.trans_le ha.1
  have hb0 : 0 < b := ha0.trans hab'
  have h₁ := compact_rank_interval_bound μ hm hlo hC hε hεκ hbound ha.1 hab hb.2
  have h₂ := compact_rank_interval_bound μ hm (mul_pos hκ hlo) hC hε hεκ hbound
    (mul_le_mul_of_nonneg_left ha.1 hκ.le) (mul_le_mul_of_nonneg_left hab hκ.le)
    ((mul_le_of_le_one_left hb0.le hκ1).trans hb.2)
  have h₃ := div_le_div_of_nonneg_left (mul_nonneg hL (sub_nonneg.mpr hab)) hlo ha.1
  have hh := (hdup a b ha0 hab' hb.2).trans
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hB) h₃)
  convert! hh using 1; ring

theorem eventually_source_low_stieltjes_IC (i : Row) :
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
      ∀ lo : ℝ, 0 < lo → lo ≤ lowEnd i →
        ∃ (F D : StieltjesFunction ℝ),
          Continuous F ∧ Continuous D ∧ IsFiniteMeasure F.measure ∧ IsFiniteMeasure D.measure ∧
          (∀ b ∈ Icc (lo/2) (lowEnd i),
            F b=sourceSuccess i m G g margin b ∧ D b=sourceDuplicate i m G g margin b) ∧
          (let C := (lowBidMeasure i G (lowEnd i)).support ∩ Icc lo (lowEnd i)
           F.measure.restrict C ≪ volume ∧ D.measure.restrict C ≪ volume ∧
             (F.measure.restrict C).withDensityᵥ (fun b => sourceRank (cutoff i) (G.map Prod.snd) b-b)=
               (volume.restrict C).withDensityᵥ (fun b =>
                 sourceSuccess i m G g margin b+eta i*sourceDuplicate i m G g margin b)+
                 (D.measure.restrict C).withDensityᵥ (fun b => eta i*b)) := by
  filter_upwards [eventually_source_low_rank_density i,eventually_source_low_used_rent i,
    eventually_sharp_absorption_small i,eventually_ge_atTop (4:ℕ)]
    with m hdensity hrentSource hsmall hm
  intro G hG hvalue hmenu hatom g K margin hg hK hKM hKfloor hlow hactive hIC lo hlo hloH
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let H := lowEnd i
  let Z := extensionEnd i
  let a₀ := lo/2
  let μ := lowBidMeasure i G H
  let Γ := lowJointMeasure i G H
  let M := sourceRank (cutoff i) Gb
  let S := sourceS i m G
  let D := sourceD i m G
  let ell := LowChernoff.physicalFloor i
  let cap := localCap i
  let C : Set ℝ := μ.support ∩ Icc lo H
  have ha₀ : 0 < a₀ := half_pos hlo
  have ha₀H : a₀ ≤ H := (show a₀ ≤ lo by dsimp [a₀]; linarith).trans hloH
  have hH : 0 < H := (lowEnd_bounds i).1
  have hHZ : H < Z := (lowEnd_bounds i).2.1
  have hZentry : Z < entry i := by
    have ht := cutoff_pos i
    linarith [(lowEnd_bounds i).2.2.1]
  have hZK : Z ≤ K := (hZentry.trans hK).le
  have hgZ : PrefixConditions (xi i) g Z := LowRankMeasures.PrefixConditions.mono hg hZK
  have hgH : PrefixConditions (xi i) g H := LowRankMeasures.PrefixConditions.mono hg (hHZ.le.trans hZK)
  have hZB : Z ≤ RankCutoff.Mstar i := (lowEnd_bounds i).2.2.2.le
  have hfloor : ∀ᵐ p ∂G, ell p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
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
  have hrentΓ : ∀ᵐ p ∂Γ, (Lm i m/10)*p.2 ≤ p.1-p.2 := by
    filter_upwards [hΓ] with p hp
    exact hrentSource G inferInstance hvalue hfloor hatom g Z (ReceiptGap.cap i) margin
      hgZ hlow hZB (by rfl) p.1 p.2 hp.2.1 hp.1.2.2.1 (hp.2.2.trans hHZ.le) hp.1.2.2.2
  have hrentμ : ∀ᵐ b ∂μ, (Lm i m/10)*b ≤ M b-b := by
    rw [← hmap]
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_le (by fun_prop) (hcM.measurable.sub measurable_id))).mpr
    filter_upwards [hrentΓ,hrankΓ] with p hp hr
    simpa only [Pi.sub_apply,id_eq,hr] using hp
  have hrentClosed : ∀ b ∈ μ.support, (Lm i m/10)*b ≤ M b-b :=
    Measure.support_subset_of_isClosed
      (isClosed_le (by fun_prop) (hcM.sub continuous_id)) hrentμ
  have hagree {b : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
      sourceSuccess i m G g margin b=S b ∧ sourceDuplicate i m G g margin b=D b :=
    source_extensions_agree i m G g hgZ hlow margin hb (hbH.trans hHZ.le)
  have hmono := actual_prefix_monotone (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    Gb (source_floor_bid_nonnegative i G hfloor) (capacity m) g hgH margin
  have hSmono : MonotoneOn S (Icc a₀ H) := by
    intro a ha b hb hab
    have hh := hmono.1 ⟨(ha₀.trans_le ha.1).le,ha.2⟩ ⟨(ha₀.trans_le hb.1).le,hb.2⟩ hab
    change sourceSuccess i m G g margin a ≤ sourceSuccess i m G g margin b at hh
    rw [(hagree (ha₀.trans_le ha.1) ha.2).1,(hagree (ha₀.trans_le hb.1) hb.2).1] at hh
    exact hh
  have hDmono : MonotoneOn D (Icc a₀ H) := by
    intro a ha b hb hab
    have hh := hmono.2 ⟨(ha₀.trans_le ha.1).le,ha.2⟩ ⟨(ha₀.trans_le hb.1).le,hb.2⟩ hab
    change sourceDuplicate i m G g margin a ≤ sourceDuplicate i m G g margin b at hh
    rw [(hagree (ha₀.trans_le ha.1) ha.2).2,(hagree (ha₀.trans_le hb.1) hb.2).2] at hh
    exact hh
  have hSc : ContinuousOn S (Icc a₀ H) := hcSD.1.mono fun b hb => ha₀.trans_le hb.1
  have hDc : ContinuousOn D (Icc a₀ H) := hcSD.2.mono fun b hb => ha₀.trans_le hb.1
  let F := ofMonotoneOn S ha₀H hSmono hSc
  let E := ofMonotoneOn D ha₀H hDmono hDc
  have hFeq {b : ℝ} (hb : b ∈ Icc a₀ H) : F b=S b := ofMonotoneOn_eq S ha₀H hSmono hSc hb
  have hEeq {b : ℝ} (hb : b ∈ Icc a₀ H) : E b=D b := ofMonotoneOn_eq D ha₀H hDmono hDc hb
  have hFc : Continuous F := ofMonotoneOn_continuous S ha₀H hSmono hSc
  have hEc : Continuous E := ofMonotoneOn_continuous D ha₀H hDmono hDc
  have hbounds {b : ℝ} (hb : b ∈ Icc a₀ H) :
      S b ∈ Icc (0:ℝ) 1 ∧ D b ∈ Icc (0:ℝ) 1 := by
    have hh := source_first_duplicate_bounds i m G g margin b
    rw [(hagree (ha₀.trans_le hb.1) hb.2).1,(hagree (ha₀.trans_le hb.1) hb.2).2] at hh
    exact hh
  have hFb : ∀ b : ℝ, F b ∈ Icc (0:ℝ) 1 := fun b => (hbounds (clip_mem ha₀H b)).1
  have hEb : ∀ b : ℝ, E b ∈ Icc (0:ℝ) 1 := fun b => (hbounds (clip_mem ha₀H b)).2
  letI : IsFiniteMeasure F.measure := finite_of_bounds F hFb
  letI : IsFiniteMeasure E.measure := finite_of_bounds E hEb
  have hden := (hdensity G inferInstance hvalue hmenu hatom g K margin hg hK hKM
    hKfloor hlow hactive hIC).2
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i ≤ 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hεκ : scaledCoefficient i m*kappa i < 1 := by
    have hh := mul_le_mul_of_nonneg_left hκ1 hsmall.1
    have hh' : scaledCoefficient i m*kappa i ≤ scaledCoefficient i m := by
      simpa only [mul_one] using hh
    exact hh'.trans_lt hsmall.2.1
  let B : ℝ := (m-1:ℕ)*pureRare m
  let L : ℝ := 2*equalRare i m/xi i
  have hB : 0 ≤ B := by dsimp [B,pureRare]; positivity
  have hL : 0 ≤ L := div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (xi_pos i).le
  have hdupSource := (source_actual_duplicate_level_and_interval i G hvalue hfloor hatom hm
    g hgH (hHZ.le.trans hlow) (hHZ.le.trans hZB) hHZ.le margin).2
  have hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ H →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (kappa i*a) (kappa i*b)))+L*(b-a)/a := by
    intro a b ha hab hb
    have hh := hdupSource a b ha hab hb
    rw [(hagree (ha.trans hab) hb).2,(hagree ha (hab.le.trans hb)).2] at hh
    have hkb : kappa i*b ≤ H := (mul_le_of_le_one_left (ha.trans hab).le hκ1).trans hb
    rw [lowBidMeasure_real_Ioc i G ha.le hb,
      lowBidMeasure_real_Ioc i G (mul_nonneg hκ.le ha.le) hkb]
    convert! hh using 1
    dsimp only [B,L]
    field_simp [(xi_pos i).ne',ha.ne']
  let LD := B*(geometricBound (kappa i) (scaledCoefficient i m) (densityConstant i) (m:ℝ) a₀+
    kappa i*geometricBound (kappa i) (scaledCoefficient i m) (densityConstant i) (m:ℝ) (kappa i*a₀))+L/a₀
  have hLD : 0 ≤ LD := by
    have h₁ : 0 < 1-scaledCoefficient i m := sub_pos.mpr hsmall.2.1
    have h₂ : 0 < 1-scaledCoefficient i m*kappa i := sub_pos.mpr hεκ
    have hC0 := (densityConstant_pos i).le
    dsimp [LD,geometricBound]
    positivity
  have hDi := duplicate_increment_of_compact_rank μ D hmR ha₀ hκ hκ1
    (densityConstant_pos i).le hsmall.2.1 hεκ hB hL hden hdup
  have hCI : C ⊆ Ioc a₀ H := fun b hb =>
    ⟨(show a₀ < lo by dsimp [a₀]; linarith).trans_le hb.2.1,hb.2.2⟩
  have hC : IsClosed C := Measure.isClosed_support.inter isClosed_Icc
  have hLm : 0 < Lm i m := (Lm_mem_Ioc i hm).1
  have hres := supported_stieltjes_identity F E hFc hEc hFb hEb M hcM hC ha₀ ha₀H hCI
    (show eta i ∈ Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ])
    (show 0 < (Lm i m/10)*lo by positivity) hLD (cutoff_pos i).le
    (fun b hb => ⟨mul_nonneg (cutoff_pos i).le measureReal_nonneg,
      (hRankK b (hb.2.2.trans hHZ.le)).trans hKcap⟩)
    (fun b hb => (mul_le_mul_of_nonneg_left hb.2.1 (by positivity : 0 ≤ Lm i m/10)).trans
      (hrentClosed b hb.1))
    (by
      intro a ha b hb hab
      rw [hEeq ha,hEeq hb]
      exact hDi a ha b hb hab)
    (by
      intro a ha b hb hbM
      have haI : a ∈ Icc a₀ H := ⟨(hCI ha).1.le,(hCI ha).2⟩
      rw [hFeq haI,hEeq haI,hFeq hb,hEeq hb]
      have hell : ell (M a)=0 := source_floor_zero ((hRankK a (ha.2.2.trans hHZ.le)).trans hKfloor)
      exact IC_on_closed_used_support μ M ell cap S D (eta i)
        hcM hcell hccap hcSD.1 hcSD.2 hIμ a ha.1 (hlo.trans_le ha.2.1) b
        (ha₀.trans_le hb.1) (by rw [hell]; exact ha₀.trans_le hb.1)
        (lt_min (lt_min hbM (hb.2.trans_lt (lowEnd_below_cap i))) (hb.2.trans_lt hHZ)))
  refine ⟨F,E,hFc,hEc,inferInstance,inferInstance,?_,hres.1,hres.2.1,?_⟩
  · intro b hb
    exact ⟨(hFeq hb).trans (hagree (ha₀.trans_le hb.1) hb.2).1.symm,
      (hEeq hb).trans (hagree (ha₀.trans_le hb.1) hb.2).2.symm⟩
  · have he : (volume.restrict C).withDensityᵥ (fun b => F b+eta i*E b)=
        (volume.restrict C).withDensityᵥ (fun b =>
          sourceSuccess i m G g margin b+eta i*sourceDuplicate i m G g margin b) := by
      apply WithDensityᵥEq.congr_ae
      filter_upwards [ae_restrict_mem hC.measurableSet] with b hb
      have hbI : b ∈ Icc a₀ H := ⟨(hCI hb).1.le,(hCI hb).2⟩
      rw [hFeq hbI,hEeq hbI,← (hagree (hlo.trans_le hb.2.1) hb.2.2).1,
        ← (hagree (hlo.trans_le hb.2.1) hb.2.2).2]
    simpa only [he] using hres.2.2

end FCAppendix.Affine.Uniform06.LiteralStieltjesIC
