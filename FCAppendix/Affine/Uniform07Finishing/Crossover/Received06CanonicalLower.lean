import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06FullLaw
import FCAppendix.Affine.Uniform06.FullRateLimit
import FCAppendix.Affine.Uniform06.SourceCoarseOutput
import FCAppendix.Affine.Uniform06.OptimizedPhysicalRate

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform07 LiteralExperiment

namespace Received06

theorem quadratic_prefactor_beats_exponential
    (m : ℕ→ℕ) (hm : Tendsto m atTop atTop) (C I : ℕ→ℝ)
    {a J J₀ : ℝ} (ha : 0< a) (hJ : 0< J) (hgap : J₀< J)
    (hcost : Tendsto (fun k=>I k/((m k-1:ℕ):ℝ)) atTop (𝓝 J₀))
    (hlower : ∀ᶠk in atTop,
      a≤ C k*Real.exp (I k)*((m k-1:ℕ):ℝ)^2)
    {K L : ℝ} (hK : 0< K) (hL : 0< L) :
    ∀ᶠk in atTop,K*Real.exp (-J*(m k:ℝ))< L*C k := by
  let r:ℝ:=(max 0 J₀+J)/2
  have hmax : max 0 J₀< J := max_lt hJ hgap
  have hr0 : 0< r := by dsimp [r]; linarith [le_max_left (0:ℝ) J₀]
  have hrI : J₀< r := by dsimp [r]; linarith [le_max_right (0:ℝ) J₀]
  have hrJ : r< J := by dsimp [r]; linarith
  have hpoly : Tendsto
      (fun k=>(m k:ℝ)^2*Real.exp (-(J-r)*(m k:ℝ))) atTop (𝓝 0) := by
    have hh:=(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (J-r)
      (sub_pos.mpr hrJ)).comp (tendsto_natCast_atTop_atTop.comp hm)
    simpa only [Real.rpow_two,Function.comp_def] using! hh
  have htol : 0< L*a/K := div_pos (mul_pos hL ha) hK
  filter_upwards [hm.eventually (eventually_ge_atTop 2),hlower,
    hcost.eventually (Iio_mem_nhds hrI),hpoly.eventually (Iio_mem_nhds htol)]
    with k hmk hl hc hp
  let n:ℝ:=((m k-1:ℕ):ℝ)
  have hn : 0< n := by dsimp [n]; exact_mod_cast (show 0< m k-1 by omega)
  have hnm : n≤(m k:ℝ) := by dsimp [n]; exact_mod_cast Nat.sub_le (m k) 1
  have hmn : 0≤(m k:ℝ) := Nat.cast_nonneg _
  have hI : I k≤ r*(m k:ℝ) := by
    have hi:=((div_lt_iff₀ hn).mp hc).le
    exact hi.trans (mul_le_mul_of_nonneg_left hnm hr0.le)
  have he : Real.exp (I k-J*(m k:ℝ))≤ Real.exp (-(J-r)*(m k:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hn2 : n^2≤(m k:ℝ)^2 := pow_le_pow_left₀ hn.le hnm 2
  have hpoly' : K*n^2*Real.exp (I k-J*(m k:ℝ))< L*a := by
    calc
      K*n^2*Real.exp (I k-J*(m k:ℝ)) ≤
          K*(m k:ℝ)^2*Real.exp (-(J-r)*(m k:ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn2 hK.le) he
          (Real.exp_pos _).le (mul_nonneg hK.le (sq_nonneg _))
      _ < L*a := by
        have hh:=mul_lt_mul_of_pos_left hp hK
        have heq : K*(L*a/K)=L*a := by field_simp [hK.ne']
        rw [heq] at hh
        simpa only [mul_assoc] using hh
  have heq : Real.exp (-J*(m k:ℝ))*Real.exp (I k)=
      Real.exp (I k-J*(m k:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hscale : 0< Real.exp (I k)*n^2 := mul_pos (Real.exp_pos _) (pow_pos hn 2)
  apply (mul_lt_mul_iff_left₀ hscale).mp
  calc
    K*Real.exp (-J*(m k:ℝ))*(Real.exp (I k)*n^2)=
        K*n^2*Real.exp (I k-J*(m k:ℝ)) := by rw [←heq]; ring
    _ < L*a := hpoly'
    _ ≤ L*(C k*Real.exp (I k)*n^2) := mul_le_mul_of_nonneg_left hl hL.le
    _ = L*C k*(Real.exp (I k)*n^2) := by ring

theorem exists_lower_bid_with_rate_gap (row : Row) {b₀ J : ℝ}
    (hb : b₀∈Ioo (cutoff row/2) (entry row))
    (hgap : canonicalRate row (b₀/cutoff row)< J) :
    ∃b∈Ioo (cutoff row/2) b₀,canonicalRate row (b/cutoff row)< J := by
  have hc:=(OptimizedPhysicalRate.canonicalRate_hasDerivAt_physical row hb).continuousAt
  have hnb : {b : ℝ | canonicalRate row (b/cutoff row)< J}∈𝓝 b₀ :=
    hc.tendsto.eventually (Iio_mem_nhds hgap)
  obtain ⟨ε,hε,hball⟩:=Metric.mem_nhds_iff.mp hnb
  let d:ℝ:=min (ε/2) ((b₀-cutoff row/2)/2)
  have hd : 0< d := lt_min (half_pos hε) (half_pos (sub_pos.mpr hb.1))
  have hdε : d<ε := (min_le_left _ _).trans_lt (by linarith)
  have hdb : d< b₀-cutoff row/2 := (min_le_right _ _).trans_lt (by linarith [hb.1])
  refine ⟨b₀-d,⟨by linarith,by linarith⟩,hball ?_⟩
  have he : b₀-d-b₀= -d := by ring
  simpa only [Metric.mem_ball,Real.dist_eq,he,abs_neg,
    abs_of_pos hd] using hdε

end Received06

namespace Received05

theorem ReadyLowerFamily.canonical_beats_exponential
    (F : ReadyLowerFamily) (row : Row) (σ : ℕ→ℕ)
    (hσ : Tendsto σ atTop atTop) {b J : ℝ}
    (hb : b∈Ioo (cutoff row/2) (entry row)) (hJ : 0< J)
    (hgap : canonicalRate row (b/cutoff row)< J)
    {K L : ℝ} (hK : 0< K) (hL : 0< L) :
    ∀ᶠk in atTop,K*Real.exp (-J*((F.start+σ k:ℕ):ℝ))<
      L*sourceCanonicalMarginal row (F.start+σ k)
        (G row (F.start+σ k) (F.law row (σ k)))
        (g row (F.start+σ k) (F.law row (σ k)))
        (cm row (F.start+σ k) (F.law row (σ k))) b := by
  let m:ℕ→ℕ:=fun k=>F.start+σ k
  let E:=fun k=>F.law row (σ k)
  let μ:=fun k=>G row (m k) (E k)
  let z:ℝ:=b/cutoff row
  let d:ℝ:=x row-z
  have ht:=cutoff_pos row
  have hb0 : 0< b := (half_pos ht).trans hb.1
  have hz : z∈Ioo (1/2:ℝ) (x row) := by
    dsimp [z]
    exact ⟨(lt_div_iff₀ ht).mpr (by linarith [hb.1]),
      (div_lt_iff₀ ht).mpr (by simpa only [entry] using hb.2)⟩
  have hd : 0< d := sub_pos.mpr hz.2
  have hdmax : d≤ x row-1/2 := by dsimp [d]; linarith [hz.1]
  have hzt : z*cutoff row=b := div_mul_cancel₀ _ ht.ne'
  have hzband : z∈Icc (1/2:ℝ) (x row-d) := by
    dsimp [d]
    exact ⟨hz.1.le,by linarith⟩
  have hm : Tendsto m atTop atTop := (Physical.tail_population_tendsto F.start).comp hσ
  have hμ : Tendsto μ atTop (𝓝 (FullJointLaw.law row)):=F.full_joint_tendsto row σ hσ
  have hcoarse:=SourceCoarseOutput.from_early_source (G row) (g row) (cm row) row
    (earlyMenu row) (roots row).literal (roots row).rejection
  obtain ⟨θ,θlo,θhi,A,hθlo,hθhi,hfinite⟩:=hcoarse.bounds d hd hdmax
  let θs:ℕ→ℝ:=fun k=>θ (m k) (E k) z
  let I:ℕ→ℝ:=fun k=>EarlyCoarseUniform.finiteCost row (m k) (μ k) z (θs k)
  let C:ℕ→ℝ:=fun k=>sourceCanonicalMarginal row (m k) (μ k)
    (g row (m k) (E k)) (cm row (m k) (E k)) b
  have hmatch : ∀ᶠk in atTop,
      SubentryTilt.mean (MixedLaw.law row (MixedLaw.physicalLowerLaw row b (μ k:Measure (ℝ×ℝ))))
        Prod.fst (θs k)=(capacity (m k):ℝ)/((m k-1:ℕ):ℝ) := by
    filter_upwards [hm.eventually hfinite] with k hk
    simpa only [θs,μ,hzt] using (hk (E k) z hzband).2.1
  obtain ⟨θ₀,hθ₀,htheta,hscore,hrate,hcost⟩:=
    FullRateLimit.original_triangular_cost_limit row μ hμ (fun _=>b) θs (fun _=>hb0)
      ⟨hz.1.le,hz.2⟩ (by simpa only [hzt] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ=>b) atTop (𝓝 b))) m hm hmatch
  have hcost' : Tendsto (fun k=>I k/((m k-1:ℕ):ℝ)) atTop (𝓝 (canonicalRate row z)) := by
    simpa only [I,EarlyCoarseUniform.finiteCost,hzt] using hcost
  have hlower : ∀ᶠk in atTop,
      1/((A:ℝ)+1)≤ C k*Real.exp (I k)*((m k-1:ℕ):ℝ)^2 := by
    filter_upwards [hm.eventually hfinite] with k hk
    simpa only [EarlyCoarseUniform.normalizedC,hzt,C,I,θs,μ] using
      (hk (E k) z hzband).2.2.1
  exact Received06.quadratic_prefactor_beats_exponential m hm C I
    (by positivity) hJ hgap hcost' hlower hK hL

end Received05
end FCAppendix.Affine.Uniform07Finishing.Crossover
