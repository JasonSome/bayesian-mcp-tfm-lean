import FCAppendix.Existence.SingletonRankLaw
import FCAppendix.Existence.RankEnvelopeProbability
import FCAppendix.Finite.PPINonrare

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter

variable {m n c : ℕ} (hn : 0<n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (b : ℝ → ℝ) (hb : Measurable b) (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    [NullSingletonClass (positiveBidMeasure F g b)]

local notation "Gamma" => singletonGame m n c hn F b hb A G g hg

theorem singletonGame_accepts_iff_rank (i : Fin m) (j : Fin n) (y : ℝ) (hy : 0 ≤ y) :
    ∀ᵐ omega ∂backgroundLaw Gamma, Accepts Gamma i y j omega ↔ rivals i (aboveAt j y) omega<c := by
  classical
  have hsingle := measure_eq_zero_iff_ae_notMem.mp
    (singletonGame_visible_atomless (m:=m) (c:=c) hn F b hb A G g hg j y)
  have hall : ∀ᵐ d ∂Measure.pi (fun _ : Fin m => userLaw Gamma),
      ∀ l, ¬(j ∈ firstK (d l).2 (d l).1.2.routeCount ∧ (d l).1.2.bid=y) :=
    ae_all_iff.mpr fun l =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Gamma) l).quasiMeasurePreserving.ae hsingle
  have hback : ∀ᵐ omega ∂backgroundLaw Gamma,
      ∀ l, ¬(j ∈ firstK (omega.1 l).2 (omega.1 l).1.2.routeCount ∧ (omega.1 l).1.2.bid=y) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hall
  filter_upwards [hback] with omega hno
  let L := presentList omega i y j
  have hL : NonnegativeList L := by
    intro l
    cases he : L l with
    | none => simp only [entryBid]; exact le_rfl
    | some a => exact presentList_bid_nonneg omega i y hy j l a he
  have hnot : ∀ l, l≠i → L l ≠ some y := by
    intro l hli hly
    exact hno l (presentList_other_some omega i l hli y j y hly)
  have hsel := HighestBid.selection_iff_rank L c hL i y hy (presentList_self omega i y j) hnot
  have heq : (Finset.univ.filter (fun l => y<entryBid (L l))) =
      (Finset.univ.erase i).filter (fun l => omega.1 l ∈ aboveAt j y) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true,aboveAt,mem_setOf_eq]
    by_cases hli : l=i
    · subst l
      simp only [L,presentList_self,entryBid,lt_self_iff_false,ne_eq,not_true_eq_false,false_and]
    · rw [show L l=if j ∈ firstK (omega.1 l).2 (omega.1 l).1.2.routeCount
        then some (omega.1 l).1.2.bid else none from presentList_other omega i l hli y j]
      by_cases hreach : j ∈ firstK (omega.1 l).2 (omega.1 l).1.2.routeCount
      · simp [hreach,entryBid,hli]
      · simp [hreach,entryBid,not_lt_of_ge hy]
  rw [heq] at hsel
  change i ∈ HighestBid.selection L c ↔ _
  simpa only [rivals_eq_card] using hsel

theorem singletonGame_acceptProb (i : Fin m) (j : Fin n) (y : ℝ) (hy : 0 ≤ y) :
    acceptProb Gamma i y j=binomBelow (m-1) ((positiveBidMeasure F g b).real (Ioi y)/(n:ℝ)) c := by
  rw [← singletonGame_alphaGt (m:=m) (c:=c) hn F b hb A G g hg j y,alphaGt,
    ← prob_rivals_lt Gamma i _ (measurableSet_aboveAt j y) c]
  apply measureReal_congr
  exact (singletonGame_accepts_iff_rank hn F b hb A G g hg i j y hy).mono fun _ hh => propext hh

theorem singletonGame_meanAcceptProb (i : Fin m) (y : ℝ) (hy : 0 ≤ y) :
    meanAcceptProb Gamma i y=binomBelow (m-1) ((positiveBidMeasure F g b).real (Ioi y)/(n:ℝ)) c := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold meanAcceptProb
  simp_rw [singletonGame_acceptProb hn F b hb A G g hg i _ y hy]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,one_div_mul_cancel hnR.ne',one_mul]

end FCAppendix.Bayes.SingletonConstruction
