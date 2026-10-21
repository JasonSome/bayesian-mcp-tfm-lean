import FCAppendix.Affine.Uniform06.SourceCoarseAsymptotics

noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyCoarseMargins

open MeasureTheory Set Filter LowBody
open scoped Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource

def floorPrice (i : Row) : ℝ := (1-xi i)*ReceiptGap.cap i

theorem floorPrice_bounds (i : Row) : 0 < floorPrice i ∧ floorPrice i < cutoff i/2 := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  refine ⟨mul_pos (sub_pos.mpr hξ1) (ReceiptGap.cap_bounds i).1,?_⟩
  have hcoef : (1-xi i)*ReceiptGap.capFactor i < (1/2:ℝ) := by
    cases i <;> norm_num [ReceiptGap.capFactor,xi,xiQ,etaQ,x,xQ,kappa,kappaQ]
  have hh := mul_lt_mul_of_pos_right hcoef (cutoff_pos i)
  simpa [floorPrice,ReceiptGap.cap_scaled,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using! hh

def finiteMargins (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (b θ : ℝ) (g : GuardData)
    (Θ lo s ε q a d : ℝ) : Prop :=
  2 ≤ m ∧ 0 < b ∧ 0 < θ ∧ θ ≤ Θ ∧
  0 < g.margin ∧ 0 < g.population ∧ 0 < g.requiredDemand ∧
  entry i-cutoff i/200 ≤ g.multiplier ∧ g.radius ≤ cutoff i/100 ∧
  0 < g.multiplier-g.radius ∧ lo < b ∧ b < s ∧ b ≤ g.multiplier ∧
  b ≤ ReceiptGap.cap i ∧ (∀ᵐ p ∂G,p.2 ≤ ReceiptGap.cap i) ∧
  (1-xi i)*ReceiptGap.cap i ≤ lo ∧
  ε*((m-1:ℕ):ℝ)+2 < ((m-1:ℕ):ℝ)*(rho-TiltedGood.upperProbability i G b θ) ∧
  2*ε*((m-1:ℕ):ℝ)+3 ≤ ((m-1:ℕ):ℝ)*(TiltedGood.lowerProbability i G b θ-
    (rho-TiltedGood.upperProbability i G b θ)) ∧
  q ≤ (TiltedGood.law i G b θ).real (CostAmplification.activeStrip s (ReceiptGap.cap i)) ∧
  12*ε ≤ q ∧ 4 ≤ q*((m-1:ℕ):ℝ) ∧
  2/((b-lo)*(q*((m-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i)) < (b-lo)/(xi i*b) ∧
  a*((m-1:ℕ):ℝ) ≤ (b-lo)*(q*((m-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i) ∧
  1+b*(m:ℝ)/lo ≤ d*((m-1:ℕ):ℝ)

set_option maxHeartbeats 400000 in

theorem eventual_source_margins (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (m : ℕ → ℕ) (b θ : ℕ → ℝ) (g : ℕ → GuardData)
    (hm : Tendsto m atTop atTop) {hi Θ : ℝ} (hhi : hi < entry i) (_hΘ : 0 < Θ)
    (hband : ∀ n,b n ∈ Icc (cutoff i/2) hi)
    (hvalue : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hcap : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ ReceiptGap.cap i)
    (hactive : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000)
    (htheta : ∀ᶠ n in atTop,0 < θ n ∧ θ n ≤ Θ)
    (hmatch : ∀ᶠ n in atTop,
      (∫ r,demand (xi i) (b n) r ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))=
        (capacity (m n):ℝ)/((m n-1:ℕ):ℝ))
    (hL : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i)))
    (hR : ∀ᶠ n in atTop,(g n).radius ≤ cutoff i/100)
    (hg : ∀ᶠ n in atTop,0 < (g n).margin ∧ 0 < (g n).population ∧ 0 < (g n).requiredDemand) :
    ∃ lo ε q a d : ℝ,0 < lo ∧ 0 < ε ∧ 0 < q ∧ 0 < a ∧ 0 < d ∧
      ∀ᶠ n in atTop,finiteMargins i (m n) (G n:Measure (ℝ × ℝ)) (b n) (θ n) (g n)
        Θ lo (entry i) ε q a d := by
  let U := ReceiptGap.cap i
  let lo := floorPrice i
  let q := Real.exp (-2*Θ)*TiltedGood.stripMass i
  let δ := TiltedGood.exposureMargin i hi (entry i) U*q
  let ε := min (q/24) (min (δ/8) (1/64000:ℝ))
  let a := (cutoff i/2-lo)*q/(2*xi i*U)
  let β := (cutoff i/2-lo)/(xi i*U)
  let d := 1+2*U/lo
  have hU : 0 < U := (ReceiptGap.cap_bounds i).1
  have hlo : 0 < lo := (floorPrice_bounds i).1
  have hblo : 0 < cutoff i/2-lo := sub_pos.mpr (floorPrice_bounds i).2
  have hq : 0 < q := mul_pos (Real.exp_pos _) (TiltedGood.stripMass_pos i)
  have hδ : 0 < δ := mul_pos (TiltedGood.exposureMargin_pos i hhi hU) hq
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have ha : 0 < a := by dsimp [a]; have hξ := xi_pos i; positivity
  have hβ : 0 < β := div_pos hblo (mul_pos (xi_pos i) hU)
  have hd : 0 < d := by dsimp [d]; positivity
  have hεq : 24*ε ≤ q := by
    have hh : ε ≤ q/24 := min_le_left _ _
    linarith
  have hεδ : 8*ε ≤ δ := by
    have hh : ε ≤ δ/8 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hεnum : ε ≤ (1/64000:ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  let bound := 12001+8/δ+4/q+4/(a*β)
  have hNb : Tendsto (fun n => ((m n-1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (PhysicalRates.rivals_tendsto.comp hm)
  have hlarge : ∀ᶠ n in atTop,bound < ((m n-1:ℕ):ℝ) := hNb.eventually (eventually_gt_atTop bound)
  have hLlo : ∀ᶠ n in atTop,entry i-cutoff i/200 < (g n).multiplier :=
    hL.eventually (Ioi_mem_nhds (by linarith [cutoff_pos i] : entry i-cutoff i/200 < entry i))
  have hLhi : ∀ᶠ n in atTop,hi < (g n).multiplier := hL.eventually (Ioi_mem_nhds hhi)
  refine ⟨lo,ε,q,a,d,hlo,hε,hq,ha,hd,?_⟩
  filter_upwards [hcap,hactive,htheta,hmatch,hg,hlarge,hLlo,hLhi,hR] with n
    hcapn hactn hθn hmatchn hgn hNn hLn hLhin hRn
  let N := ((m n-1:ℕ):ℝ)
  have hboundparts : 0 < 8/δ ∧ 0 < 4/q ∧ 0 < 4/(a*β) :=
    ⟨div_pos (by norm_num) hδ,div_pos (by norm_num) hq,div_pos (by norm_num) (mul_pos ha hβ)⟩
  have hN12000 : 12000 < N := by
    dsimp only [bound,N] at hNn ⊢
    linarith only [hNn,hboundparts.1,hboundparts.2.1,hboundparts.2.2]
  have hNδ : 8/δ < N := by
    dsimp only [bound,N] at hNn ⊢
    linarith only [hNn,hboundparts.1,hboundparts.2.1,hboundparts.2.2]
  have hNq : 4/q < N := by
    dsimp only [bound,N] at hNn ⊢
    linarith only [hNn,hboundparts.1,hboundparts.2.1,hboundparts.2.2]
  have hNβ : 4/(a*β) < N := by
    dsimp only [bound,N] at hNn ⊢
    linarith only [hNn,hboundparts.1,hboundparts.2.1,hboundparts.2.2]
  have hN : 0 < N := by linarith
  have hm2 : 2 ≤ m n := by
    have hh : 0 < m n-1 := Nat.cast_pos.mp hN
    omega
  have hbpos : 0 < b n := (half_pos (cutoff_pos i)).trans_le (hband n).1
  have hbU : b n ≤ U := (hband n).2.trans (hhi.trans (ReceiptGap.entry_below_cap i)).le
  have hlb : lo < b n := (floorPrice_bounds i).2.trans_le (hband n).1
  have hbs : b n < entry i := (hband n).2.trans_lt hhi
  have hguard : 0 < (g n).multiplier-(g n).radius := by
    have hx : (3/200:ℝ) < x i := by cases i <;> norm_num [x,xQ]
    have ht := mul_lt_mul_of_pos_right hx (cutoff_pos i)
    change (3/200:ℝ)*cutoff i < x i*cutoff i at ht
    change entry i-cutoff i/200 < (g n).multiplier at hLn
    unfold entry at hLn
    nlinarith
  have hqOrig := TiltedGood.early_original_strip_mass i (G n:Measure (ℝ × ℝ))
    (hvalue n) hcapn hactn (show entry i ≤ EarlyRankCeiling.prefixEnd i by
      unfold EarlyRankCeiling.prefixEnd; linarith [cutoff_pos i])
  have hstrip : q ≤ (TiltedGood.law i (G n:Measure (ℝ × ℝ)) (b n) (θ n)).real
      (CostAmplification.activeStrip (entry i) U) :=
    TiltedGood.tilted_strip_mass_lower i (G n:Measure (ℝ × ℝ)) hbpos hθn.1.le hθn.2 hqOrig
  have hres := TiltedGood.matching_residual_margins i (G n:Measure (ℝ × ℝ)) hm2 hbpos
    (hband n).2 hhi hU hθn.1.le hθn.2 hqOrig hmatchn
  have hres0 : δ-1/N ≤ rho-TiltedGood.upperProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n) := by
    simpa only [δ,q,mul_assoc,N,U] using hres.1
  have hres1 := hres.2
  have hpos : ε*N+2 < N*(rho-TiltedGood.upperProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) := by
    have hm0 := mul_le_mul_of_nonneg_left hres0 hN.le
    have heq : N*(δ-1/N)=N*δ-1 := by field_simp [hN.ne']
    rw [heq] at hm0
    have hδN : 8 < δ*N := by
      have hh := (div_lt_iff₀ hδ).mp hNδ
      nlinarith
    have hεN := mul_le_mul_of_nonneg_right hεδ hN.le
    nlinarith only [hm0,hδN,hεN]
  have hroom : 2*ε*N+3 ≤ N*(TiltedGood.lowerProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n)-
      (rho-TiltedGood.upperProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n))) := by
    have hh := mul_le_mul_of_nonneg_left hres1 hN.le
    have he := mul_le_mul_of_nonneg_right hεnum hN.le
    nlinarith only [hh,he,hN12000]
  have hAN : a*N ≤ (b n-lo)*(q*N/2)/(xi i*U) := by
    have hh := mul_le_mul_of_nonneg_right (sub_le_sub_right (hband n).1 lo)
      (show 0 ≤ q*N by positivity)
    have hdv := div_le_div_of_nonneg_right hh (show 0 ≤ 2*xi i*U by have hξ := xi_pos i; positivity)
    calc
      a*N = (cutoff i/2-lo)*(q*N)/(2*xi i*U) := by dsimp only [a]; ring
      _ ≤ (b n-lo)*(q*N)/(2*xi i*U) := hdv
      _ = (b n-lo)*(q*N/2)/(xi i*U) := by ring
  have hratio : β ≤ (b n-lo)/(xi i*b n) := by
    calc
      _ ≤ (b n-lo)/(xi i*U) := div_le_div_of_nonneg_right
        (sub_le_sub_right (hband n).1 lo) (mul_pos (xi_pos i) hU).le
      _ ≤ _ := div_le_div_of_nonneg_left (sub_pos.mpr hlb).le
        (mul_pos (xi_pos i) hbpos) (mul_le_mul_of_nonneg_left hbU (xi_pos i).le)
  have hsmall : 2/(a*N) < β := by
    apply (div_lt_iff₀ (mul_pos ha hN)).mpr
    have hh := (div_lt_iff₀ (mul_pos ha hβ)).mp hNβ
    nlinarith only [hh]
  have hwindow : 2/((b n-lo)*(q*N/2)/(xi i*U)) < (b n-lo)/(xi i*b n) :=
    ((div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2:ℝ)) (mul_pos ha hN) hAN).trans_lt hsmall).trans_le hratio
  have hmN : (m n:ℝ)=N+1 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 1 ≤ m n)]
    norm_num
  have hD : 1+b n*(m n:ℝ)/lo ≤ d*N := by
    rw [hmN]
    have hNN : N+1 ≤ 2*N := by linarith
    have hm := mul_le_mul hbU hNN (by linarith : 0 ≤ N+1) hU.le
    have hdv := div_le_div_of_nonneg_right hm hlo.le
    dsimp only [d]
    have hform : (U*(2*N))/lo=(2*U/lo)*N := by ring
    rw [hform] at hdv
    nlinarith only [hdv,hN12000]
  exact ⟨hm2,hbpos,hθn.1,hθn.2,hgn.1,hgn.2.1,hgn.2.2,hLn.le,hRn,hguard,
    hlb,hbs,(hband n).2.trans hLhin.le,hbU,hcapn,le_rfl,hpos,hroom,hstrip,
    by linarith,by
      have hh := (div_lt_iff₀ hq).mp hNq
      nlinarith,
    hwindow,hAN,hD⟩

end FCAppendix.Affine.Uniform06.EarlyCoarseMargins
