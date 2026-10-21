import FCAppendix.Affine.Hybrid.ClassifiedPolicy
import FCAppendix.Finite.ReceiptBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set Classical

namespace ContextPolicy
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C : ContextPolicy m c Seed)

lemma upperPart_nonnegative {U : ℝ} (L : LocalList m) (hL : NonnegativeList L) :
    NonnegativeList (upperPart U L) := by
  intro i
  unfold upperPart
  split_ifs
  · exact hL i
  · exact le_rfl

lemma upper_selection_iff_highest {U b : ℝ} (L : LocalList m) (hL : NonnegativeList L)
    (j : Fin 2) (s : Seed) (i : Fin m) (hi : L i=some b) (hb : U<b) :
    i∈C.selection U j L s ↔ i∈HighestBid.selection (upperPart U L) c := by
  have hiU : i∈upperSet U L:=by simp [upperSet,hi,TaggedLocal.tag,not_le.mpr hb]
  by_cases hc : TaggedLocal.localCount U U L 2 ≤ c
  · have hcard : (Finset.univ.filter (fun k=>upperPart U L k≠none)).card ≤ c:=by
      have he : Finset.univ.filter (fun k=>upperPart U L k≠none)=upperSet U L:=by
        ext k
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,upperPart_present_iff]
      rw [he,upperSet_card]
      exact hc
    rw [HighestBid.selection_fills_spare _ c (upperPart_nonnegative L hL) hcard]
    simp only [selection,if_pos hc,Finset.mem_union,hiU,true_or,
      Finset.mem_filter,Finset.mem_univ,true_and,upperPart_present_iff]
  · simp only [selection,if_neg hc]

lemma upper_selection_iff_rank {U b : ℝ} (hU : 0 ≤ U) (L : LocalList m)
    (hL : NonnegativeList L) (j : Fin 2) (s : Seed) (i : Fin m)
    (hi : L i=some b) (hb : U<b) (hno : ∀k,k≠i→L k≠some b) :
    i∈C.selection U j L s ↔ (Finset.univ.filter (fun k=>b<entryBid (L k))).card<c := by
  have hiP : upperPart U L i=some b:=by simp [upperPart,hi,TaggedLocal.tag,not_le.mpr hb]
  have hnoP : ∀k,k≠i→upperPart U L k≠some b:=by
    intro k hk
    unfold upperPart
    split_ifs
    · exact hno k hk
    · simp
  have hrank : (Finset.univ.filter (fun k=>b<entryBid (upperPart U L k)))=
      Finset.univ.filter (fun k=>b<entryBid (L k)) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    cases he : L k with
    | none=>simp [upperPart,he,TaggedLocal.tag,entryBid]
    | some a=>
      by_cases ha : a ≤ U
      · simp [upperPart,he,TaggedLocal.tag,ha,entryBid,not_lt.mpr (ha.trans hb.le),
          not_lt.mpr (hU.trans hb.le)]
      · simp [upperPart,he,TaggedLocal.tag,ha]
  rw [C.upper_selection_iff_highest L hL j s i hi hb]
  rw [HighestBid.selection_iff_rank _ c (upperPart_nonnegative L hL) i b
    (hU.trans hb.le) hiP hnoP,hrank]

variable (Gamma : FiniteGame m 2 c Seed) {U : ℝ}
local notation "G"=>C.nativeGame Gamma U

theorem native_upper_accepts_iff_rank (hU : 0 ≤ U) (hatom : ∀(j : Fin 2)(b : ℝ),U<b→userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : U<y) :
    ∀ᵐomega ∂backgroundLaw G,Accepts G i y j omega ↔ rivals i (aboveAt j y) omega<c := by
  have hsingle:=measure_eq_zero_iff_ae_notMem.mp (hatom j y hy)
  have hall : ∀ᵐd ∂userProfileLaw G,
      ∀k,¬(j∈firstK (d k).2 (d k).1.2.routeCount ∧ (d k).1.2.bid=y):=
    ae_all_iff.mpr (fun k=>(measurePreserving_eval (fun _ : Fin m=>userLaw G) k).quasiMeasurePreserving.ae hsingle)
  have hback : ∀ᵐomega ∂backgroundLaw G,
      ∀k,¬(j∈firstK (omega.1 k).2 (omega.1 k).1.2.routeCount ∧ (omega.1 k).1.2.bid=y):=
    measurePreserving_fst.quasiMeasurePreserving.ae hall
  filter_upwards [hback] with omega hno
  let L:=presentList omega i y j
  have hL : NonnegativeList L:=by
    intro k
    cases he : L k with
    | none=>simp only [entryBid];exact le_rfl
    | some a=>exact presentList_bid_nonneg omega i y (hU.trans hy.le) j k a he
  have hn : ∀k,k≠i→L k≠some y:=fun k hk hky=>
    hno k (presentList_other_some omega i k hk y j y hky)
  have hs:=C.upper_selection_iff_rank hU L hL j (omega.2 j) i (presentList_self omega i y j) hy hn
  have heq : (Finset.univ.filter (fun k=>y<entryBid (L k)))=
      (Finset.univ.erase i).filter (fun k=>omega.1 k∈aboveAt j y) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true,aboveAt,mem_setOf_eq]
    by_cases hk : k=i
    · subst k
      simp only [L,presentList_self,entryBid,lt_self_iff_false,ne_eq,not_true_eq_false,false_and]
    · rw [show L k=if j∈firstK (omega.1 k).2 (omega.1 k).1.2.routeCount
        then some (omega.1 k).1.2.bid else none from presentList_other omega i k hk y j]
      by_cases hr : j∈firstK (omega.1 k).2 (omega.1 k).1.2.routeCount
      · simp [hr,entryBid,hk]
      · simp [hr,entryBid,not_lt_of_ge (hU.trans hy.le)]
  rw [heq] at hs
  change i∈C.selection U j L (omega.2 j) ↔ _
  simpa only [rivals_eq_card] using hs

theorem native_upper_acceptProb (hU : 0 ≤ U) (hatom : ∀(j : Fin 2)(b : ℝ),U<b→userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : U<y) :
    acceptProb G i y j=binomBelow (m-1) (alphaGt G j y) c := by
  rw [alphaGt,←prob_rivals_lt G i _ (measurableSet_aboveAt j y) c]
  apply measureReal_congr
  exact (C.native_upper_accepts_iff_rank Gamma hU hatom i j y hy).mono (fun _ hh=>propext hh)

theorem native_upper_meanAcceptProb (hU : 0 ≤ U) (hatom : ∀(j : Fin 2)(b : ℝ),U<b→userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (y : ℝ) (hy : U<y) :
    meanAcceptProb G i y=binomBelow (m-1) (alphaGt G 0 y) c := by
  unfold meanAcceptProb
  simp_rw [C.native_upper_acceptProb Gamma hU hatom i _ y hy,alphaGt_eq G _ 0]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end ContextPolicy
end FCAppendix.Affine.Hybrid
