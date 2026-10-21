import FCAppendix.Affine.Tail04.SourceAmbientLaws
import FCAppendix.Affine.Tail04.ZeroNoiseActive
import FCAppendix.Affine.Tail04.UnequalZeroNoisePrivate

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceBoxCoherence
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateAmbient CompactSourceBidLaws

lemma sortedBox_widen {N : ℕ} {B C : ℝ} (h : B≤ C) (b : Fin N→ Icc (1:ℝ) B) :
    SortedAllNoise.sortedBox (fun i=> widen h (b i))=
      fun i=> widen h (SortedAllNoise.sortedBox b i) := by
  funext i
  apply Subtype.ext
  rfl

lemma signal_update {H : ℕ} {R V W : ℝ} (h : V≤ W) (s : Signal H R V)
    (j : Fin H) (p : Icc R V) :
    signal h (Function.update s j (Sum.inr p))=
      Function.update (signal h s) j (Sum.inr (widen h p)) := by
  funext k
  by_cases hk : k=j
  · subst k
    simp only [signal,Function.update_self,entry,Sum.map_inr]
  · simp only [signal,Function.update_of_ne hk]

lemma privateValue_widen {N H c : ℕ} {R V W B C ξ : ℝ}
    (hV : V≤ W) (hB : B≤ C) (hξ : 0< ξ)
    (b : Fin N→ Icc (1:ℝ) B) (μ : WeakProbability.Law (Signal H R V))
    (s : Signal H R V) (j : Fin H) (p : Icc R V) :
    PrivatePayoffContinuity.privateValue (c:=c) ξ j
      (fun i=>(SortedAllNoise.sortedBox (fun k=> widen hB (b k)) i:ℝ),
        policyMean N H c R W ξ 1 C
          (SortedAllNoise.sortedBox (fun k=> widen hB (b k)),law hV μ),
        Function.update (signal hV s) j (Sum.inr (widen hV p)))=
    PrivatePayoffContinuity.privateValue (c:=c) ξ j
      (fun i=>(SortedAllNoise.sortedBox b i:ℝ),
        policyMean N H c R V ξ 1 B (SortedAllNoise.sortedBox b,μ),
        Function.update s j (Sum.inr p)) := by
  rw [sortedBox_widen,←signal_update]
  have hq:=policyMean_parameter (c:=c) hV hB hξ (SortedAllNoise.sortedBox b,μ)
  change policyMean N H c R W ξ 1 C
    ((fun i=> widen hB (SortedAllNoise.sortedBox b i)),law hV μ)=_ at hq
  rw [hq]
  exact privateValue_signal hV _ _ _ j

lemma activeCount_widen {N H c : ℕ} {R V W B C ξ : ℝ}
    (hV : V≤ W) (hB : B≤ C) (hξ : 0< ξ)
    (b : Fin N→ Icc (1:ℝ) B) (μ : WeakProbability.Law (Signal H R V)) (i : Fin N) :
    EqualPrivateCountPayoff.countLaw N H c R W ξ 1 C ((fun k=> widen hB (b k)),law hV μ) i=
      EqualPrivateCountPayoff.countLaw N H c R V ξ 1 B (b,μ) i := by
  have hq:=congrFun (policyMean_parameter (c:=c) hV hB hξ (b,μ)) i
  unfold EqualPrivateCountPayoff.countLaw
  simp only [parameter] at hq
  simp only [hq]

lemma rankInclusion_widen (N H0 H1 c : ℕ) {R V W : ℝ} (h : V≤ W) (side : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (p : ℝ)
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) R V) :
    AtypicalPartialNoisy.rankInclusion N H0 H1 c side j (p,signal h s)=
      AtypicalPartialNoisy.rankInclusion N H0 H1 c side j (p,s) := by
  have he : AtypicalPartialNoisy.rivalsAbove j p (signal h s)=
      AtypicalPartialNoisy.rivalsAbove j p s := by
    ext k
    simp only [AtypicalPartialNoisy.rivalsAbove,Finset.mem_filter,signal,partialBid_entry]
    cases s k <;> rfl
  simp only [AtypicalPartialNoisy.rankInclusion,he]

lemma equal_count_sorted_widen {N H c : ℕ} {R V W B C ξ : ℝ}
    (hV : V≤ W) (hB : B≤ C) (hξ : 0< ξ)
    (b : Fin N→ Icc (1:ℝ) B) (μ : WeakProbability.Law (Signal H R V)) (i : Fin N) :
    EqualPrivateCountPayoff.countLaw N H c R W ξ 1 C
      ((fun k=> widen hB (b k)),law hV μ) i=
    EqualPrivateCountPayoff.countLaw N H c R V ξ 1 B (SortedAllNoise.sortedBox b,μ)
      (SortedAllNoise.focalRank (fun k=>(b k:ℝ)) i) := by
  rw [activeCount_widen hV hB hξ]
  exact (EqualPrivateActiveRelabel.countLaw_sorted hξ b μ i).symm

end FCAppendix.Affine.Tail04.SourceBoxCoherence
