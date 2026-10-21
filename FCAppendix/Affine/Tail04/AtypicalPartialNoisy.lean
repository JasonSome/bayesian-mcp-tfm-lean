import FCAppendix.Affine.Tail04.AtypicalPartialRanks
import FCAppendix.Affine.Tail04.PrivatePayoffContinuity
import FCAppendix.Exclusive.MarkerConstruction

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalPartialNoisy
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper AllCountAtypical AtypicalPartialRanks LocalHighCommon AtypicalUnequal

local instance (H : ℕ) : TopologicalSpace (Finset (Fin H)) := ⊥
local instance (H : ℕ) : DiscreteTopology (Finset (Fin H)) := ⟨rfl⟩
local instance (H : ℕ) : MeasurableSpace (Finset (Fin H)) := ⊤
local instance (H : ℕ) : BorelSpace (Finset (Fin H)) := ⟨borel_eq_top_of_discrete.symm⟩

def rivalsAbove {H : ℕ} {R V : ℝ} (j : Fin H) (t : ℝ) (s : Signal H R V) :
    Finset (Fin H) :=
  (Finset.univ.erase j).filter fun k => isUpper (s k)=true ∨ t< partialBid (s k)

def rankAccept (N H0 H1 c : ℕ) (side : Bool) (k : ℕ) : Prop :=
  if EitherSlack N H0 H1 c then
    if N+ownCount H0 H1 side< c then True else k< c
  else if N+H0+H1≤2*c then True
  else if N≤2*c then (owners N H0 c (fun _ => 1) side).card+k< c else False

def rankInclusion (N H0 H1 c : ℕ) {R V : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : ℝ × Signal (ownCount H0 H1 side) R V) : ℝ :=
  if rankAccept N H0 H1 c side (rivalsAbove j p.1 p.2).card then 1 else 0

lemma rankInclusion_bounds (N H0 H1 c : ℕ) {R V : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : ℝ × Signal (ownCount H0 H1 side) R V) :
    0≤ rankInclusion N H0 H1 c side j p ∧ rankInclusion N H0 H1 c side j p≤1 := by
  unfold rankInclusion
  split_ifs <;> norm_num

lemma measurable_rivalsAbove {H : ℕ} {R V : ℝ} (j : Fin H) :
    Measurable (fun p : ℝ × Signal H R V => rivalsAbove j p.1 p.2) := by
  apply Exclusive.Marker.measurable_filter (Finset.univ.erase j)
  intro k
  exact (measurableSet_eq_fun
    (continuous_isUpper.measurable.comp ((measurable_pi_apply k).comp measurable_snd))
    measurable_const).union
      (measurableSet_lt measurable_fst
        (continuous_partialBid.measurable.comp ((measurable_pi_apply k).comp measurable_snd)))

lemma measurable_rankInclusion (N H0 H1 c : ℕ) {R V : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) :
    Measurable (rankInclusion N H0 H1 c (R:=R) (V:=V) side j) :=
  (measurable_of_countable (fun K : Finset (Fin (ownCount H0 H1 side)) =>
    if rankAccept N H0 H1 c side K.card then (1:ℝ) else 0)).comp (measurable_rivalsAbove j)

lemma privateHigher_eq_rivalsAbove {H : ℕ} {R V Rm : ℝ}
    (row : Row H R V Rm) (j : Fin H) (price : Icc R V)
    (hj : row j=Sum.inr price) (_hprice : 0<(price:ℝ)) (hfloor : (price:ℝ)< Rm) :
    privateHigher row price=(rivalsAbove j price (signal row)).card := by
  unfold privateHigher
  congr 1
  ext k
  by_cases hkj : k=j
  · subst k
    simp [rivalsAbove,hj,numericalEntry]
  · cases hk : row k with
    | inl upper =>
      have hh : (price:ℝ)<(upper:ℝ) := hfloor.trans_le upper.2
      simp [rivalsAbove,hkj,hk,numericalEntry,signal,signalEntry,isUpper,hh]
    | inr partialBidValue =>
      simp [rivalsAbove,hkj,hk,numericalEntry,signal,signalEntry,isUpper,partialBid]

theorem actual_inclusion_eq_rank (N H0 H1 c : ℕ) {ξ B R V Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R V Rm)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (hRRm : R≤ Rm) (hV : V<1) (hgap : (1-ξ)*B< R)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R V) (hj : row j=Sum.inr price)
    (hfloor : V< Rm) (hno : ∀ k, k≠j → numericalEntry (row k)≠(price:ℝ)) :
    (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side row then (1:ℝ) else 0)=
      rankInclusion N H0 H1 c side j ((price:ℝ),signal row) := by
  have he := selected_partial_iff N H0 H1 c side b row hξ hb hR hRRm hV hgap j price hj hno
  have hbchange := partialRule_congr_bids N H0 H1 c b (fun _ => 1) side row price
  have hr := privateHigher_eq_rivalsAbove row j price hj (hR.trans_le price.2.1)
    (price.2.2.trans_lt hfloor)
  simp only [he,hbchange]
  simp only [partialRule,rankInclusion,rankAccept,hr]

lemma rivalsAbove_eventually_eq {H : ℕ} {R V : ℝ} (j : Fin H)
    (p : ℝ × Signal H R V)
    (hno : ∀ k, k≠j → partialBid (p.2 k)≠p.1) :
    ∀ᶠ q in 𝓝 p, rivalsAbove j q.1 q.2=rivalsAbove j p.1 p.2 := by
  have hi (k : Fin H) : ∀ᶠ q in 𝓝 p,
      k∈rivalsAbove j q.1 q.2 ↔ k∈rivalsAbove j p.1 p.2 := by
    by_cases hkj : k=j
    · subst k
      exact Eventually.of_forall fun q => by simp [rivalsAbove]
    · have hmark : ∀ᶠ q : ℝ × Signal H R V in 𝓝 p,
          isUpper (q.2 k)=isUpper (p.2 k) :=
        ((isOpen_discrete ({isUpper (p.2 k)} : Set Bool)).preimage
          (continuous_isUpper.comp ((continuous_apply k).comp continuous_snd))).mem_nhds rfl
      have hb : Continuous (fun q : ℝ × Signal H R V => partialBid (q.2 k)) :=
        continuous_partialBid.comp ((continuous_apply k).comp continuous_snd)
      have ht : ∀ᶠ q : ℝ × Signal H R V in 𝓝 p,
          q.1 < partialBid (q.2 k) ↔ p.1 < partialBid (p.2 k) := by
        rcases lt_or_gt_of_ne (hno k hkj) with hk | hk
        · have hevent : ∀ᶠ q : ℝ × Signal H R V in 𝓝 p, partialBid (q.2 k) < q.1 :=
            (isOpen_lt hb continuous_fst).mem_nhds hk
          exact hevent.mono (fun q hq => iff_of_false (not_lt.mpr hq.le) (not_lt.mpr hk.le))
        · have hevent : ∀ᶠ q : ℝ × Signal H R V in 𝓝 p, q.1 < partialBid (q.2 k) :=
            (isOpen_lt continuous_fst hb).mem_nhds hk
          exact hevent.mono (fun q hq => iff_of_true hq hk)
      filter_upwards [hmark,ht] with q hq hqt
      simp only [rivalsAbove,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,
        and_true,hq,hqt]
  exact (Filter.eventually_all.mpr hi).mono fun q hq => Finset.ext hq

lemma continuousAt_rankInclusion (N H0 H1 c : ℕ) {R V : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : ℝ × Signal (ownCount H0 H1 side) R V)
    (hno : ∀ k, k≠j → partialBid (p.2 k)≠p.1) :
    ContinuousAt (rankInclusion N H0 H1 c side j) p := by
  apply (continuousAt_const : ContinuousAt
    (fun _ : ℝ × Signal (ownCount H0 H1 side) R V => rankInclusion N H0 H1 c side j p) p).congr
  exact (rivalsAbove_eventually_eq j p hno).mono fun q hq => by
    simp only [rankInclusion,hq]

abbrev FocalInput (H : ℕ) (R U eps : ℝ) := Icc R U × Signal H R (U*(1+eps))

def inputAt {H : ℕ} {R U eps : ℝ} (p : FocalInput H R U eps) (u : unitInterval) :
    ℝ × Signal H R (U*(1+eps)) := (Hybrid.activeNoisyRealBid eps p.1 u,p.2)

lemma continuous_inputAt {H : ℕ} {R U eps : ℝ} :
    Continuous (fun z : FocalInput H R U eps × unitInterval => inputAt z.1 z.2) := by
  unfold inputAt Hybrid.activeNoisyRealBid
  fun_prop

lemma ae_inputAt_no_tie {H : ℕ} {R U eps : ℝ} (hR : 0< R) (heps : eps≠0)
    (j : Fin H) (p : FocalInput H R U eps) :
    ∀ᵐ u : unitInterval ∂volume, ∀ k, k≠j →
      partialBid ((inputAt p u).2 k)≠(inputAt p u).1 := by
  apply ae_all_iff.mpr
  intro k
  filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps p.1 (partialBid (p.2 k))
    heps (hR.trans_le p.1.2.1).ne'] with u hu _
  exact hu.symm

def smoothedInclusion (N H0 H1 c : ℕ) {R U eps : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : FocalInput (ownCount H0 H1 side) R U eps) : ℝ :=
  ∫ u : unitInterval, rankInclusion N H0 H1 c side j (inputAt p u)

def smoothedPayment (N H0 H1 c : ℕ) {R U eps : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : FocalInput (ownCount H0 H1 side) R U eps) : ℝ :=
  ∫ u : unitInterval, (inputAt p u).1*rankInclusion N H0 H1 c side j (inputAt p u)

theorem continuous_smoothedInclusion (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : eps≠0) (side : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (smoothedInclusion N H0 H1 c (R:=R) (U:=U) (eps:=eps) side j) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun p u => rankInclusion N H0 H1 c side j (inputAt p u)) (bound:=fun _ => (1:ℝ))
  · exact Eventually.of_forall fun p => ((measurable_rankInclusion N H0 H1 c side j).comp
      ((continuous_inputAt.comp (continuous_const.prodMk continuous_id)).measurable)).aestronglyMeasurable
  · exact Eventually.of_forall fun p => ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rankInclusion_bounds N H0 H1 c side j _).1]
      exact (rankInclusion_bounds N H0 H1 c side j _).2
  · exact integrable_const 1
  · filter_upwards [ae_inputAt_no_tie hR heps j p] with u hu
    exact (continuousAt_rankInclusion N H0 H1 c side j _ hu).comp
      (f := fun q : FocalInput (ownCount H0 H1 side) R U eps => inputAt q u)
      ((continuous_inputAt.comp (continuous_id.prodMk continuous_const)).continuousAt)

theorem continuous_smoothedPayment (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : 0< eps) (side : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (smoothedPayment N H0 H1 c (R:=R) (U:=U) (eps:=eps) side j) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun p u => (inputAt p u).1*rankInclusion N H0 H1 c side j (inputAt p u))
    (bound:=fun _ => |U*(1+eps)|)
  · exact Eventually.of_forall fun p =>
      (((continuous_fst.comp continuous_inputAt).comp
        (continuous_const.prodMk continuous_id)).measurable.mul
          ((measurable_rankInclusion N H0 H1 c side j).comp
            ((continuous_inputAt.comp (continuous_const.prodMk continuous_id)).measurable))).aestronglyMeasurable
  · exact Eventually.of_forall fun p => ae_of_all _ fun u => by
      have hbid := Hybrid.activeNoisyRealBid_mem hR heps.le p.1 u
      have hp : 0≤(inputAt p u).1 := hR.le.trans hbid.1
      have hi := rankInclusion_bounds N H0 H1 c side j (inputAt p u)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp hi.1)]
      exact (mul_le_of_le_one_right hp hi.2).trans (hbid.2.trans (le_abs_self _))
  · exact integrable_const _
  · filter_upwards [ae_inputAt_no_tie hR heps.ne' j p] with u hu
    exact ((continuous_fst.comp continuous_inputAt).comp
      (continuous_id.prodMk continuous_const)).continuousAt.mul
        ((continuousAt_rankInclusion N H0 H1 c side j _ hu).comp
          (f := fun q : FocalInput (ownCount H0 H1 side) R U eps => inputAt q u)
          ((continuous_inputAt.comp (continuous_id.prodMk continuous_const)).continuousAt))

def noisyRow {H : ℕ} {R U eps Rm : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (j : Fin H) (b : Icc R U) (row : Row H R (U*(1+eps)) Rm) (u : unitInterval) :
    Row H R (U*(1+eps)) Rm :=
  Function.update row j (Sum.inr
    ⟨Hybrid.activeNoisyRealBid eps b u,Hybrid.activeNoisyRealBid_mem hR heps b u⟩)

theorem ae_actual_inclusion_eq_rank (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    ∀ᵐ u : unitInterval ∂volume,
      (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps.le j price row u) then (1:ℝ) else 0)=
      rankInclusion N H0 H1 c side j (inputAt (price,signal row) u) := by
  have hno (k : Fin (ownCount H0 H1 side)) : ∀ᵐ u : unitInterval ∂volume,
      k≠j → numericalEntry (noisyRow hR heps.le j price row u k)≠
        Hybrid.activeNoisyRealBid eps price u := by
    filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps price (numericalEntry (row k))
      heps.ne' (hR.trans_le price.2.1).ne'] with u hu hkj
    simpa only [noisyRow,Function.update_of_ne hkj] using hu.symm
  filter_upwards [ae_all_iff.mpr hno] with u hu
  let price' : Icc R (U*(1+eps)) :=
    ⟨Hybrid.activeNoisyRealBid eps price u,Hybrid.activeNoisyRealBid_mem hR heps.le price u⟩
  rw [actual_inclusion_eq_rank N H0 H1 c side b _ hξ hb hR hRRm hV hgap j price'
    (by simp [noisyRow,price']) hfloor hu]
  have hr : rivalsAbove j (Hybrid.activeNoisyRealBid eps price u)
      (signal (noisyRow hR heps.le j price row u))=
      rivalsAbove j (Hybrid.activeNoisyRealBid eps price u) (signal row) := by
    ext k
    by_cases hkj : k=j
    · subst k
      simp [rivalsAbove]
    · simp [rivalsAbove,noisyRow,signal,Function.update_of_ne hkj]
  simp only [rankInclusion,inputAt,price',hr]
  rfl

theorem actual_smoothedInclusion (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    (∫ u : unitInterval, if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps.le j price row u) then (1:ℝ) else 0)=
      smoothedInclusion N H0 H1 c side j (price,signal row) :=
  integral_congr_ae (ae_actual_inclusion_eq_rank N H0 H1 c side b row hξ hb hR heps
    hRRm hV hgap hfloor j price)

theorem actual_smoothedPayment (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    (∫ u : unitInterval, Hybrid.activeNoisyRealBid eps price u*
      (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps.le j price row u) then (1:ℝ) else 0))=
      smoothedPayment N H0 H1 c side j (price,signal row) := by
  apply integral_congr_ae
  filter_upwards [ae_actual_inclusion_eq_rank N H0 H1 c side b row hξ hb hR heps
    hRRm hV hgap hfloor j price] with u hu
  rw [hu]
  rfl

abbrev AveragingInput (H : ℕ) (R U eps : ℝ) :=
  Icc R U × ProbabilityMeasure (Signal H R (U*(1+eps)))

def averagedInclusion (N H0 H1 c : ℕ) {R U eps : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : AveragingInput (ownCount H0 H1 side) R U eps) : ℝ :=
  ∫ s, smoothedInclusion N H0 H1 c side j (p.1,s)
    ∂(p.2 : Measure (Signal (ownCount H0 H1 side) R (U*(1+eps))))

def averagedPayment (N H0 H1 c : ℕ) {R U eps : ℝ} (side : Bool)
    (j : Fin (ownCount H0 H1 side)) (p : AveragingInput (ownCount H0 H1 side) R U eps) : ℝ :=
  ∫ s, smoothedPayment N H0 H1 c side j (p.1,s)
    ∂(p.2 : Measure (Signal (ownCount H0 H1 side) R (U*(1+eps))))

theorem continuous_averagedInclusion (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : eps≠0) (side : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (averagedInclusion N H0 H1 c (R:=R) (U:=U) (eps:=eps) side j) :=
  Existence.Distributional.continuous_law_integral _
    (continuous_smoothedInclusion N H0 H1 c hR heps side j)

theorem continuous_averagedPayment (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : 0< eps) (side : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (averagedPayment N H0 H1 c (R:=R) (U:=U) (eps:=eps) side j) :=
  Existence.Distributional.continuous_law_integral _
    (continuous_smoothedPayment N H0 H1 c hR heps side j)

theorem continuous_averagedUtility (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : 0< eps) (side : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (fun p : ℝ × AveragingInput (ownCount H0 H1 side) R U eps =>
      p.1*averagedInclusion N H0 H1 c side j p.2-
        averagedPayment N H0 H1 c side j p.2) :=
  (continuous_fst.mul ((continuous_averagedInclusion N H0 H1 c hR heps.ne' side j).comp
    continuous_snd)).sub ((continuous_averagedPayment N H0 H1 c hR heps side j).comp continuous_snd)

def originalSignalLaw {H : ℕ} {R V Rm : ℝ}
    (θ : Measure (Row H R V Rm)) [IsProbabilityMeasure θ] : ProbabilityMeasure (Signal H R V) :=
  ⟨θ.map signal,Measure.isProbabilityMeasure_map continuous_signal.measurable.aemeasurable⟩

theorem original_averagedInclusion (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ)
    (θ : Measure (Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    (∫ row, (∫ u : unitInterval, if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps.le j price row u) then (1:ℝ) else 0) ∂θ)=
      averagedInclusion N H0 H1 c side j (price,originalSignalLaw θ) := by
  calc
    _ = ∫ row, smoothedInclusion N H0 H1 c side j (price,signal row) ∂θ :=
      integral_congr_ae (ae_of_all _ fun row => actual_smoothedInclusion N H0 H1 c
        side b row hξ hb hR heps hRRm hV hgap hfloor j price)
    _ = _ := by
      unfold averagedInclusion originalSignalLaw
      exact (integral_map continuous_signal.measurable.aemeasurable
        (((continuous_smoothedInclusion N H0 H1 c hR heps.ne' side j).comp
          (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)).symm

theorem original_averagedPayment (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ)
    (θ : Measure (Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    (∫ row, (∫ u : unitInterval, Hybrid.activeNoisyRealBid eps price u*
      (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps.le j price row u) then (1:ℝ) else 0)) ∂θ)=
      averagedPayment N H0 H1 c side j (price,originalSignalLaw θ) := by
  calc
    _ = ∫ row, smoothedPayment N H0 H1 c side j (price,signal row) ∂θ :=
      integral_congr_ae (ae_of_all _ fun row => actual_smoothedPayment N H0 H1 c
        side b row hξ hb hR heps hRRm hV hgap hfloor j price)
    _ = _ := by
      unfold averagedPayment originalSignalLaw
      exact (integral_map continuous_signal.measurable.aemeasurable
        (((continuous_smoothedPayment N H0 H1 c hR heps side j).comp
          (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)).symm

def branchInclusion (N H0 H1 c : ℕ) {R U eps : ℝ} (side reg : Bool)
    (j : Fin (ownCount H0 H1 side))
    (p : unitInterval × AveragingInput (ownCount H0 H1 side) R U eps) : ℝ :=
  (p.1:ℝ)*(if reg then 0 else 1)+(1-(p.1:ℝ))*averagedInclusion N H0 H1 c side j p.2

def branchPayment (N H0 H1 c : ℕ) {R U eps : ℝ} (side reg : Bool)
    (j : Fin (ownCount H0 H1 side))
    (p : unitInterval × AveragingInput (ownCount H0 H1 side) R U eps) : ℝ :=
  (p.1:ℝ)*(if reg then 0 else ∫ u : unitInterval, Hybrid.activeNoisyRealBid eps p.2.1 u)+
    (1-(p.1:ℝ))*averagedPayment N H0 H1 c side j p.2

lemma continuous_averagePrice {R U eps : ℝ} :
    Continuous (fun b : Icc R U => ∫ u : unitInterval, Hybrid.activeNoisyRealBid eps b u) := by
  have he (b : Icc R U) : (∫ u : unitInterval, Hybrid.activeNoisyRealBid eps b u)=
      (b:ℝ)*(∫ u : unitInterval, 1+eps*(u:ℝ)) := by
    exact integral_const_mul _ _
  simp_rw [he]
  exact continuous_subtype_val.mul continuous_const

theorem continuous_branchInclusion (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : eps≠0) (side reg : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (branchInclusion N H0 H1 c (R:=R) (U:=U) (eps:=eps) side reg j) := by
  unfold branchInclusion
  exact ((continuous_subtype_val.comp continuous_fst).mul continuous_const).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_averagedInclusion N H0 H1 c hR heps side j).comp continuous_snd))

theorem continuous_branchPayment (N H0 H1 c : ℕ) {R U eps : ℝ}
    (hR : 0< R) (heps : 0< eps) (side reg : Bool) (j : Fin (ownCount H0 H1 side)) :
    Continuous (branchPayment N H0 H1 c (R:=R) (U:=U) (eps:=eps) side reg j) := by
  unfold branchPayment
  have hc : Continuous (fun p : unitInterval × AveragingInput (ownCount H0 H1 side) R U eps =>
      if reg then (0:ℝ) else ∫ u : unitInterval, Hybrid.activeNoisyRealBid eps p.2.1 u) := by
    cases reg
    · exact continuous_averagePrice.comp (continuous_fst.comp continuous_snd)
    · exact continuous_const
  exact ((continuous_subtype_val.comp continuous_fst).mul hc).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_averagedPayment N H0 H1 c hR heps side j).comp continuous_snd))

end FCAppendix.Affine.Tail04.AtypicalPartialNoisy
