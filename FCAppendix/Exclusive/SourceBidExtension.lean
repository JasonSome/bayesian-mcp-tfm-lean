import FCAppendix.Exclusive.SourceCentralScale
import FCAppendix.Exclusive.NarrowExistenceGameStationary

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open Exclusive.Narrow.Existence

def normalizedType (eps : ℝ) (heps : 0 ≤ eps) (v : ℝ) : ValueBand eps :=
  Set.projIcc (1-eps) (1+eps) (by linarith) v

theorem continuous_normalizedType (eps : ℝ) (heps : 0 ≤ eps) :
    Continuous (normalizedType eps heps) := continuous_projIcc (h := by linarith)

theorem normalizedType_coe (eps : ℝ) (heps : 0 ≤ eps) (v : ValueBand eps) :
    normalizedType eps heps (v : ℝ)=v := Set.projIcc_val _ v

def extendedSourceBid (eps : ℝ) (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (v : ℝ) : ℝ :=
  scale*Real.exp (beta (normalizedType eps heps (v/H)))

theorem continuous_extendedSourceBid (eps : ℝ) (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta) :
    Continuous (extendedSourceBid eps heps H scale beta) :=
  continuous_const.mul (Real.continuous_exp.comp
    (hbeta.comp ((continuous_normalizedType eps heps).comp (continuous_id.div_const H))))

theorem extendedSourceBid_high {eps H : ℝ} (heps : 0 ≤ eps) (hH : H ≠ 0)
    (scale : ℝ) (beta : ValueBand eps → ℝ) (v : ValueBand eps) :
    extendedSourceBid eps heps H scale beta (H*(v : ℝ)) = scale*Real.exp (beta v) := by
  have he : (H*(v : ℝ))/H=(v : ℝ) := by field_simp
  rw [extendedSourceBid,he,normalizedType_coe]

theorem extendedSourceBid_pos {eps : ℝ} (heps : 0 ≤ eps) (H : ℝ)
    {scale : ℝ} (hscale : 0 < scale) (beta : ValueBand eps → ℝ) (v : ℝ) :
    0 < extendedSourceBid eps heps H scale beta v := mul_pos hscale (Real.exp_pos _)

theorem extendedSourceBid_band {eps : ℝ} (heps : 0 ≤ eps) (H : ℝ)
    {scale delta : ℝ} (hscale : 0 ≤ scale) (beta : ValueBand eps → ℝ)
    (hbeta : ∀ u, beta u ∈ Icc (-delta) delta) (v : ℝ) :
    extendedSourceBid eps heps H scale beta v ∈
      Icc (scale*Real.exp (-delta)) (scale*Real.exp delta) :=
  ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbeta _).1) hscale,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbeta _).2) hscale⟩

theorem extendedSourceBid_high_strictMono {eps H : ℝ} (heps : 0 ≤ eps)
    (hH : H ≠ 0) {scale : ℝ} (hscale : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : StrictMono beta) :
    StrictMono (fun v : ValueBand eps =>
      extendedSourceBid eps heps H scale beta (H*(v : ℝ))) := by
  intro u v huv
  simp only [extendedSourceBid_high heps hH scale beta]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (hbeta huv)) hscale

theorem highValue_normalization {eps H v : ℝ} (heps : 0 ≤ eps) (hH : 0 < H)
    (hv : v ∈ Icc (H*(1-eps)) (H*(1+eps))) :
    H*(normalizedType eps heps (v/H) : ℝ)=v := by
  have hu : v/H ∈ Icc (1-eps) (1+eps) :=
    ⟨(le_div_iff₀ hH).mpr (by simpa only [mul_comm] using hv.1),
      (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hv.2)⟩
  have hp : normalizedType eps heps (v/H)=⟨v/H,hu⟩ := normalizedType_coe eps heps ⟨v/H,hu⟩
  rw [hp]
  field_simp

end FCAppendix.Bayes.ExclusiveConstruction
