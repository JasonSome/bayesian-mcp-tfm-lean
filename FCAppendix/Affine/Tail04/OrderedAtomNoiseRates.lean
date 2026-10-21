import FCAppendix.Affine.Tail04.SourceMovingMenuRates
import FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomNoiseRates
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceTailCapGap OrderedOriginalNoisySequence

theorem sequence_eventually_tail_noise
    (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M<t)
    (N : ℕ) (S : Sequence D P t ht N) {Amax k : ℝ} (hk : k<1/(2*Amax)) :
    ∀ᶠ j in atTop,(S.data j).eps*(S.data j).U≤ stripWidth Amax k/(4*t) := by
  have hlim : Tendsto (fun j => (S.eps j:ℝ)*D.U) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_mul] using S.noise_real_tendsto.mul_const D.U
  have hpos : 0< stripWidth Amax k/(4*t) :=
    div_pos (stripWidth_pos hk) (mul_pos (by norm_num) (P.M_pos.trans ht))
  have hh := hlim.eventually (gt_mem_nhds hpos)
  simpa using! hh.mono (fun j hj=> hj.le)

end FCAppendix.Affine.Tail04.OrderedAtomNoiseRates
