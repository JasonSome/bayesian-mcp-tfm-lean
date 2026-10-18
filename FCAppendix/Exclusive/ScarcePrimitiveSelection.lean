import FCAppendix.Exclusive.PrimitiveCDF
import FCAppendix.Exclusive.SourceCentralScale
import FCAppendix.Exclusive.SourceStationaryGame

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open ExclusiveSource

theorem exists_high_center (g eps : ℝ) (hg : 0 ≤ g) (heps : 0 < eps) :
    ∃ H : ℝ, 0 < H ∧ 1 ≤ H ∧ g/H ∈ Icc (0:ℝ) eps ∧ g/H < eps ∧ g/H < 1/4 := by
  let e := min eps (1/4)
  have he : 0 < e := lt_min heps (by norm_num)
  obtain ⟨H,hH⟩ := exists_gt (max 1 (g/e))
  have hH1 : 1 < H := (le_max_left _ _).trans_lt hH
  have hH0 : 0 < H := zero_lt_one.trans hH1
  have hge : g/e < H := (le_max_right _ _).trans_lt hH
  have hgH : g/H < e := (div_lt_iff₀ hH0).mpr (by
    have hh := (div_lt_iff₀ he).mp hge
    simpa only [mul_comm] using hh)
  have hsmall : g/H < eps := hgH.trans_le (min_le_left _ _)
  exact ⟨H,hH0,hH1.le,⟨div_nonneg hg hH0.le,hsmall.le⟩,hsmall,
    hgH.trans_le (min_le_right _ _)⟩

theorem normalized_low_band_separation {d : ℕ} {scaleLo q H g eps : ℝ}
    (K : LowMarketConstants (d+1) scaleLo q)
    (hscaleLo : scaleLo ≤ 1) (hH : 0 < H) (heps : eps ≤ 1/4)
    (hg : g/H < 1/4) : g+H*K.lowUpper < H*(1-eps) := by
  have hlow : K.lowUpper < 1/2 := K.low_lt_half_scaleLo.trans_le (by linarith)
  have hl := mul_lt_mul_of_pos_left hlow hH
  have hbase := (div_lt_iff₀ hH).mp hg
  have hwidth := mul_le_mul_of_nonneg_left heps hH.le
  nlinarith

theorem bandPrimitive_efficient_cutoff {d : ℕ} {rho H eps g L : ℝ}
    (h : unitInterval) (nu : Measure (Icc (1-eps) (1+eps)))
    [IsProbabilityMeasure nu] (hH : 0 < H) (hL : 0 < L)
    (hseparate : g+L < H*(1-eps))
    (hhbeta : (h : ℝ) < ((d+1:ℕ):ℝ)*rho) (hbeta : ((d+1:ℕ):ℝ)*rho < 1) :
    let vStar := g+L*(1-((d+1:ℕ):ℝ)*rho)/(1-(h : ℝ))
    vStar ∈ Ioo g (g+L) ∧
      (bandPrimitive h H nu g L).real (Iic vStar)=1-((d+1:ℕ):ℝ)*rho ∧
      (bandPrimitive h H nu g L).real (Ioi vStar)=((d+1:ℕ):ℝ)*rho := by
  exact scarce_efficient_cutoff h (scaledHighLaw H nu) g hL hseparate
    ((scaledHighLaw_supported hH nu).mono fun _ hv => hv.1) hhbeta hbeta

end FCAppendix.Bayes.ExclusiveConstruction
