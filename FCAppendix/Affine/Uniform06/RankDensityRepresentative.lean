import FCAppendix.Affine.Uniform06.LiteralRankDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

noncomputable section
namespace FCAppendix.Affine.Uniform06.RankDensityRepresentative

open MeasureTheory Set Filter Topology
open ScaledMeasure WeightedBorelContraction
open LiteralRankDensity LowRankMeasures SourceSharpDensityConstants
open LiteralExperiment LiteralPrefixStieltjes LiteralWeakRent LiteralKernelDecomposition Rank
open FCAppendix.Affine.Uniform07

def density (μ : Measure ℝ) (b : ℝ) : ℝ := (μ.rnDeriv volume b).toReal

def geometricBound (κ ε C m b : ℝ) : ℝ :=
  C*(1/(1-ε*κ)+(1/(m*b))/(1-ε))

theorem measurable_density (μ : Measure ℝ) : Measurable (density μ) :=
  (Measure.measurable_rnDeriv μ volume).ennreal_toReal

theorem density_nonnegative (μ : Measure ℝ) (b : ℝ) : 0 ≤ density μ b := ENNReal.toReal_nonneg

theorem density_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hAC : μ ≪ volume) (A : Set ℝ) : ∫ b in A, density μ b=μ.real A :=
  Measure.setIntegral_toReal_rnDeriv hAC A

theorem ae_le_of_set_integrals (ν : Measure ℝ) {f g : ℝ → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (h : ∀ A : Set ℝ, MeasurableSet A → (∫ x in A, f x ∂ν) ≤ ∫ x in A, g x ∂ν) :
    f ≤ᵐ[ν] g := by
  let A := {x | g x < f x}
  have hAm : MeasurableSet A := measurableSet_lt hgm hfm
  have hfiA : IntegrableOn f A ν := hfi.integrableOn
  have hgiA : IntegrableOn g A ν := hgi.integrableOn
  have hi := hfiA.sub hgiA
  have hn : ∀ᵐ x ∂ν.restrict A, 0 ≤ f x-g x := by
    filter_upwards [ae_restrict_mem hAm] with x hx
    exact sub_nonneg.mpr hx.le
  have hz : (∫ x in A, f x-g x ∂ν)=0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hn)
    rw [integral_sub hfiA hgiA]
    exact sub_nonpos.mpr (h A hAm)
  have he : ∀ᵐ x ∂ν.restrict A, f x-g x=0 :=
    (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [(ae_restrict_iff' hAm).mp he] with x hx
  by_contra hnot
  have hh := hx (lt_of_not_ge hnot)
  linarith

theorem geometricBound_integral {κ ε C m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo)
    {A : Set ℝ} (hA : A ⊆ Icc lo hi) :
    (∫ b in A, geometricBound κ ε C m b)=
      C*(volume.real A/(1-ε*κ)+(∫ b in A, 1/(m*b))/(1-ε)) := by
  have hc : IntegrableOn (fun _ : ℝ => 1/(1-ε*κ)) A :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => 1/(1-ε*κ)) (Icc lo hi)).integrableOn_Icc.mono_set hA
  have hr := (reciprocal_integrableOn hm hlo hA).div_const (1-ε)
  unfold geometricBound
  rw [integral_const_mul,integral_add hc hr,integral_div,integral_div,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  ring

theorem ae_density_bound_from_integrated
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hAC : μ ≪ volume)
    {κ ε C m hi : ℝ} (hm : 0 < m) (_hε : ε < 1) (_hεκ : ε*κ < 1)
    (hbound : ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo hi →
      μ.real A ≤ C*(volume.real A/(1-ε*κ)+(∫ b in A, 1/(m*b))/(1-ε))) :
    ∀ᵐ b ∂volume, b ∈ Ioc (0:ℝ) hi → density μ b ≤ geometricBound κ ε C m b := by
  have hcompact (lo : ℝ) (hlo : 0 < lo) :
      ∀ᵐ b ∂volume.restrict (Icc lo hi), density μ b ≤ geometricBound κ ε C m b := by
    have hfi : Integrable (density μ) (volume.restrict (Icc lo hi)) :=
      Measure.integrableOn_toReal_rnDeriv (measure_ne_top μ (Icc lo hi))
    have hgc : ContinuousOn (geometricBound κ ε C m) (Icc lo hi) := by
      have hr : ContinuousOn (fun b : ℝ => 1/(m*b)) (Icc lo hi) :=
        continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
          (fun b hb => mul_ne_zero hm.ne' (hlo.trans_le hb.1).ne')
      unfold geometricBound
      exact continuousOn_const.mul (continuousOn_const.add (hr.div_const _))
    have hgi : IntegrableOn (geometricBound κ ε C m) (Icc lo hi) volume := hgc.integrableOn_Icc
    apply ae_le_of_set_integrals (volume.restrict (Icc lo hi)) (measurable_density μ)
      (by unfold geometricBound; fun_prop) hfi hgi
    intro A hAm
    rw [Measure.restrict_restrict hAm]
    have hsub : A ∩ Icc lo hi ⊆ Icc lo hi := inter_subset_right
    rw [density_integral μ hAC,geometricBound_integral hm hlo hsub]
    exact hbound lo hlo (A ∩ Icc lo hi) (hAm.inter measurableSet_Icc) hsub
  have hall : ∀ n : ℕ, ∀ᵐ b ∂volume,
      b ∈ Icc (1/((n:ℝ)+1)) hi → density μ b ≤ geometricBound κ ε C m b := by
    intro n
    exact (ae_restrict_iff' measurableSet_Icc).mp (hcompact (1/((n:ℝ)+1)) (by positivity))
  filter_upwards [ae_all_iff.mpr hall] with b hb hbI
  obtain ⟨n,hn⟩ := exists_nat_gt (1/b)
  have hsmall : 1/((n:ℝ)+1) ≤ b := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    have hh := (div_lt_iff₀ hbI.1).mp hn
    nlinarith
  exact hb n ⟨hsmall,hbI.2⟩

theorem geometricBound_eq (κ ε C m b : ℝ) :
    geometricBound κ ε C m b=C*(1/(1-ε*κ)+1/((1-ε)*m*b)) := by
  unfold geometricBound
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem eventually_source_rank_density_representative (i : Row) :
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
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ b, 0 ≤ f b) ∧
        (∀ A : Set ℝ, (∫ b in A, f b)=(lowBidMeasure i G (lowEnd i)).real A) ∧
        (∀ᵐ b ∂volume, b ∈ Ioc (0:ℝ) (lowEnd i) →
          f b ≤ densityConstant i*(1/(1-scaledCoefficient i m*kappa i)+
            1/((1-scaledCoefficient i m)*(m:ℝ)*b))) := by
  filter_upwards [eventually_source_low_rank_density i,eventually_sharp_absorption_small i,
    eventually_ge_atTop (4:ℕ)] with m hsource hsmall hm
  intro G hG hvalue hmenu hatom g K margin hg hK hKM hKfloor hlow hactive hIC
  letI := hG
  have hs := hsource G hG hvalue hmenu hatom g K margin hg hK hKM hKfloor hlow hactive hIC
  let μ := lowBidMeasure i G (lowEnd i)
  have hAC : μ ≪ volume := hs.1
  have hκ1 : kappa i ≤ 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hεκ : scaledCoefficient i m*kappa i < 1 :=
    (mul_le_mul_of_nonneg_left hκ1 hsmall.1).trans_lt (by simpa using hsmall.2.1)
  have hd := ae_density_bound_from_integrated μ hAC
    (show 0 < (m:ℝ) by exact_mod_cast (show 0 < m by omega)) hsmall.2.1 hεκ hs.2
  refine ⟨density μ,measurable_density μ,density_nonnegative μ,density_integral μ hAC,?_⟩
  simpa only [geometricBound_eq] using hd

end FCAppendix.Affine.Uniform06.RankDensityRepresentative
