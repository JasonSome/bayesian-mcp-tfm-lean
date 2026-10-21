import FCAppendix.Affine.Uniform06.CrossoverRankDensity
import FCAppendix.Affine.Uniform06.LiteralStieltjesIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.CrossoverStieltjesIC

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralRankIC LowRankMeasures LiteralWeakRent LiteralLowDuplicate LiteralSuccessLower
open SourceRankRates PureRankCounts PureRankProbability EqualCanonicalRegularity
open CanonicalPrefixLipschitz CrossoverRankPreparation CrossoverRankDensity
open LiteralStieltjesIC RankDensityRepresentative ScaledMeasure CompactStieltjes SupportedStieltjesIC
open FCAppendix.Affine.Uniform07

theorem eventually_source_crossover_stieltjes_IC (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
        (min p.1 (ReceiptGap.cap i))) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (H Z K err : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      0 < H → H < Z → Z ≤ K → Z < ReceiptGap.cap i → entry i < K →
      K ≤ entry i+cutoff i/400 → PrefixConditions (xi i) g K →
      extensionEnd i ≤ g.multiplier-g.radius →
      Z+err < ActiveGraphComponent.activeBid i K →
      (∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ err) →
      (∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
          payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) →
      ∀ lo : ℝ, 0 < lo → lo ≤ H → ∃ (F E : StieltjesFunction ℝ),
        Continuous F ∧ Continuous E ∧ IsFiniteMeasure F.measure ∧ IsFiniteMeasure E.measure ∧
        (∀ b ∈ Icc (lo/2) H,
          F b=sourceSuccess i m G g margin b ∧ E b=sourceDuplicate i m G g margin b) ∧
        (let C := (lowBidMeasure i G H).support ∩ Icc lo H
         F.measure.restrict C ≪ volume ∧ E.measure.restrict C ≪ volume ∧
           (F.measure.restrict C).withDensityᵥ (fun b => sourceRank (cutoff i) (G.map Prod.snd) b-b)=
             (volume.restrict C).withDensityᵥ (fun b =>
               sourceSuccess i m G g margin b+eta i*sourceDuplicate i m G g margin b)+
             (E.measure.restrict C).withDensityᵥ (fun b => eta i*b)) := by
  filter_upwards [eventually_source_crossover_rank_density i,eventually_source_rare_small i,
    eventually_ge_atTop (4:ℕ)] with m hdensity hrare hm
  intro G hG hvalue hmenu hatom g H Z K err margin hH hHZ hZK hZcap hK hKfloor hg
    hlow hgap hactive hIC lo hlo hloH
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := lowBidMeasure i G H
  let M := sourceRank (cutoff i) Gb
  let s := CrossoverRankPreparation.S i m G g margin Z
  let d := CrossoverRankPreparation.D i m G g margin Z
  let a₀ := lo/2
  let C : Set ℝ := μ.support ∩ Icc lo H
  have ha₀ : 0 < a₀ := half_pos hlo
  have ha₀H : a₀ ≤ H := (show a₀ ≤ lo by dsimp [a₀]; linarith).trans hloH
  have hgH := LowRankMeasures.PrefixConditions.mono hg (hHZ.le.trans hZK)
  have hgZ := LowRankMeasures.PrefixConditions.mono hg hZK
  have hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
  have hp := prepare_source i hm hrare.1 G hvalue hmenu hatom g hH hHZ hZK hK hKfloor
    hg hlow hgap hactive margin hIC
  have hcM : Continuous M := hp.rank_continuous
  have hcSD := hp.kernel_continuous
  have hcoeff := physical_coefficients i hm hrare.2
  have hKcap : K ≤ cutoff i := by
    have hh : x i+1/400 < 1 := by cases i <;> norm_num [x,xQ]
    have hu := mul_lt_mul_of_pos_right hh (cutoff_pos i)
    have hKfloor' := hKfloor
    unfold entry at hKfloor'
    linarith
  have hKM : K < RankCutoff.Mstar i := by
    change K < (x i+1/200)*cutoff i
    have hKfloor' := hKfloor
    unfold entry at hKfloor'
    linarith [cutoff_pos i]
  have hHM : H ≤ RankCutoff.Mstar i := (hHZ.le.trans hZK).trans hKM.le
  have hagree {b : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
      sourceSuccess i m G g margin b=s b ∧ sourceDuplicate i m G g margin b=d b :=
    CrossoverRankPreparation.source_extensions_agree i m G g hgZ margin hb (hbH.trans hHZ.le)
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i ≤ 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hmono := actual_prefix_monotone (cutoff_mem i) (xi_pos i) hξ1 hκ hκ1 Gb
    (source_floor_bid_nonnegative i G hfloor) (capacity m) g hgH margin
  have hsmono : MonotoneOn s (Icc a₀ H) := by
    intro a ha b hb hab
    have hh := hmono.1 ⟨(ha₀.trans_le ha.1).le,ha.2⟩ ⟨(ha₀.trans_le hb.1).le,hb.2⟩ hab
    change sourceSuccess i m G g margin a ≤ sourceSuccess i m G g margin b at hh
    rw [(hagree (ha₀.trans_le ha.1) ha.2).1,(hagree (ha₀.trans_le hb.1) hb.2).1] at hh
    exact hh
  have hdmono : MonotoneOn d (Icc a₀ H) := by
    intro a ha b hb hab
    have hh := hmono.2 ⟨(ha₀.trans_le ha.1).le,ha.2⟩ ⟨(ha₀.trans_le hb.1).le,hb.2⟩ hab
    change sourceDuplicate i m G g margin a ≤ sourceDuplicate i m G g margin b at hh
    rw [(hagree (ha₀.trans_le ha.1) ha.2).2,(hagree (ha₀.trans_le hb.1) hb.2).2] at hh
    exact hh
  have hsc : ContinuousOn s (Icc a₀ H) := hcSD.1.mono fun b hb => ha₀.trans_le hb.1
  have hdc : ContinuousOn d (Icc a₀ H) := hcSD.2.mono fun b hb => ha₀.trans_le hb.1
  let F := ofMonotoneOn s ha₀H hsmono hsc
  let E := ofMonotoneOn d ha₀H hdmono hdc
  have hFeq {b : ℝ} (hb : b ∈ Icc a₀ H) : F b=s b := ofMonotoneOn_eq s ha₀H hsmono hsc hb
  have hEeq {b : ℝ} (hb : b ∈ Icc a₀ H) : E b=d b := ofMonotoneOn_eq d ha₀H hdmono hdc hb
  have hFc : Continuous F := ofMonotoneOn_continuous s ha₀H hsmono hsc
  have hEc : Continuous E := ofMonotoneOn_continuous d ha₀H hdmono hdc
  have hbounds {b : ℝ} (hb : b ∈ Icc a₀ H) : s b ∈ Icc (0:ℝ) 1 ∧ d b ∈ Icc (0:ℝ) 1 := by
    have hh := source_first_duplicate_bounds i m G g margin b
    rw [(hagree (ha₀.trans_le hb.1) hb.2).1,(hagree (ha₀.trans_le hb.1) hb.2).2] at hh
    exact hh
  have hFb : ∀ b : ℝ, F b ∈ Icc (0:ℝ) 1 := fun b => (hbounds (clip_mem ha₀H b)).1
  have hEb : ∀ b : ℝ, E b ∈ Icc (0:ℝ) 1 := fun b => (hbounds (clip_mem ha₀H b)).2
  letI : IsFiniteMeasure F.measure := finite_of_bounds F hFb
  letI : IsFiniteMeasure E.measure := finite_of_bounds E hEb
  have hden := (hdensity G inferInstance hvalue hmenu hatom g H Z K err margin hH hHZ hZK hZcap hK
    hKfloor hg hlow hgap hactive hIC).2
  have hε0 : 0 ≤ contraction i m := hcoeff.2.2.2.1
  have hε1 : contraction i m < 1 := hcoeff.2.2.2.2
  have hεκ : contraction i m*kappa i < 1 :=
    (mul_le_mul_of_nonneg_left hκ1 hε0).trans_lt (by simpa only [mul_one] using hε1)
  have hC0 : 0 ≤ densityCoefficient i m g H := by
    have hr := hcoeff.2.1
    have hA := hcoeff.1
    unfold densityCoefficient
    positivity
  have hL0 := (canonicalConstant_pos (xi_pos i) hH.le hgH).le
  have hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ H →
      d b-d a ≤ duplicateCoefficient m*(μ.real (Ioc a b)+
        μ.real (Ioc (kappa i*a) (kappa i*b)))+canonicalConstant (xi i) g H*(b-a)/a := by
    intro a b ha hab hb
    have hh := source_duplicate_interval i hm G hvalue hfloor hatom g hgH hHM margin ha hab hb
    rw [(hagree (ha.trans hab) hb).2,(hagree ha (hab.le.trans hb)).2] at hh
    have hkb : kappa i*b ≤ H := (mul_le_of_le_one_left (ha.trans hab).le hκ1).trans hb
    rw [lowBidMeasure_real_Ioc i G ha.le hb,
      lowBidMeasure_real_Ioc i G (mul_nonneg hκ.le ha.le) hkb]
    exact hh
  let LD := duplicateCoefficient m*(geometricBound (kappa i) (contraction i m)
      (densityCoefficient i m g H) 1 a₀+
    kappa i*geometricBound (kappa i) (contraction i m) (densityCoefficient i m g H) 1 (kappa i*a₀))+
      canonicalConstant (xi i) g H/a₀
  have hLD : 0 ≤ LD := by
    have h₁ := sub_pos.mpr hε1
    have h₂ := sub_pos.mpr hεκ
    have hE0 := hcoeff.2.2.1
    dsimp [LD,geometricBound]
    positivity
  have hden' : ∀ a : ℝ, 0 < a → ∀ T : Set ℝ, MeasurableSet T → T ⊆ Icc a H →
      μ.real T ≤ densityCoefficient i m g H*(volume.real T/(1-contraction i m*kappa i)+
        (∫ b in T, 1/((1:ℝ)*b))/(1-contraction i m)) := by
    simpa only [one_mul] using hden
  have hDi := duplicate_increment_of_compact_rank μ d zero_lt_one ha₀ hκ hκ1 hC0 hε1 hεκ
    hcoeff.2.2.1 hL0 hden' hdup
  have hCI : C ⊆ Ioc a₀ H := fun b hb =>
    ⟨(show a₀ < lo by dsimp [a₀]; linarith).trans_le hb.2.1,hb.2.2⟩
  have hC : IsClosed C := Measure.isClosed_support.inter isClosed_Icc
  have hq : 0 < rentCoefficient i m*lo := mul_pos hcoeff.2.1 hlo
  have hres := supported_stieltjes_identity F E hFc hEc hFb hEb M hcM hC ha₀ ha₀H hCI
    (show eta i ∈ Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ]) hq hLD (cutoff_pos i).le
    (fun b hb => ⟨mul_nonneg (cutoff_pos i).le measureReal_nonneg,
      (hp.rank_le b (hb.2.2.trans hHZ.le)).trans hKcap⟩)
    (fun b hb => (mul_le_mul_of_nonneg_left hb.2.1 hcoeff.2.1.le).trans
      (hp.rent_on_support b hb.1))
    (by
      intro a ha b hb hab
      rw [hEeq ha,hEeq hb]
      exact hDi a ha b hb hab)
    (by
      intro a ha b hb hbM
      have haI : a ∈ Icc a₀ H := ⟨(hCI ha).1.le,(hCI ha).2⟩
      rw [hFeq haI,hEeq haI,hFeq hb,hEeq hb]
      have hell : LowChernoff.physicalFloor i (M a)=0 :=
        source_floor_zero ((hp.rank_le a (ha.2.2.trans hHZ.le)).trans hKfloor)
      exact IC_on_closed_used_support μ M (LowChernoff.physicalFloor i) (cap i Z) s d (eta i)
        hcM (LowChernoff.continuous_physicalFloor i) (by unfold cap; fun_prop)
        hcSD.1 hcSD.2 hp.rank_IC a ha.1 (hlo.trans_le ha.2.1) b (ha₀.trans_le hb.1)
        (by rw [hell]; exact ha₀.trans_le hb.1)
        (lt_min (lt_min hbM (hb.2.trans_lt (hHZ.trans hZcap))) (hb.2.trans_lt hHZ)))
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

end FCAppendix.Affine.Uniform06.CrossoverStieltjesIC
