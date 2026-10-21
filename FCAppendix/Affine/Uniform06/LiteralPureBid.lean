import FCAppendix.Affine.Uniform06.LiteralRankIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralPureBid

open MeasureTheory Set Filter Topology
open LiteralRankIC LiteralPrefixStieltjes LiteralWeakRent
open LiteralExperiment PureRankCounts Rank
open FCAppendix.Affine.Uniform07

def lowerBidSet (C : Set (ℝ × ℝ)) (v : ℝ) : Set ℝ :=
  insert 0 {b | ∃ p ∈ C, p.1 < v ∧ p.2=b}

def bidEnvelope (C : Set (ℝ × ℝ)) (v : ℝ) : ℝ :=
  sSup (lowerBidSet C v)

theorem lowerBidSet_nonempty (C : Set (ℝ × ℝ)) (v : ℝ) :
    (lowerBidSet C v).Nonempty := ⟨0,Or.inl rfl⟩

theorem lowerBidSet_bddAbove {C : Set (ℝ × ℝ)} {U : ℝ}
    (hU : 0 ≤ U) (hbound : ∀ p ∈ C, p.2 ≤ U) (v : ℝ) :
    BddAbove (lowerBidSet C v) := by
  refine ⟨U,?_⟩
  rintro b (rfl | ⟨p,hp,_,rfl⟩)
  · exact hU
  · exact hbound p hp

theorem bidEnvelope_bounds {C : Set (ℝ × ℝ)} {U : ℝ}
    (hU : 0 ≤ U) (hbound : ∀ p ∈ C, p.2 ≤ U) (v : ℝ) :
    0 ≤ bidEnvelope C v ∧ bidEnvelope C v ≤ U := by
  constructor
  · exact le_csSup (lowerBidSet_bddAbove hU hbound v) (Or.inl rfl)
  · apply csSup_le (lowerBidSet_nonempty C v)
    rintro b (rfl | ⟨p,hp,_,rfl⟩)
    · exact hU
    · exact hbound p hp

theorem bidEnvelope_monotone {C : Set (ℝ × ℝ)} {U : ℝ}
    (hU : 0 ≤ U) (hbound : ∀ p ∈ C, p.2 ≤ U) :
    Monotone (bidEnvelope C) := by
  intro v w hvw
  apply csSup_le (lowerBidSet_nonempty C v)
  intro b hb
  apply le_csSup (lowerBidSet_bddAbove hU hbound w)
  rcases hb with rfl | ⟨p,hp,hpv,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨p,hp,hpv.trans_le hvw,rfl⟩

theorem bidEnvelope_le_used {C : Set (ℝ × ℝ)} {K : ℝ}
    (hnonneg : ∀ p ∈ C, 0 ≤ p.2)
    (hsort : ∀ p ∈ C, p.1 < K → ∀ q ∈ C, p.1 < q.1 → p.2 ≤ q.2)
    {p : ℝ × ℝ} (hp : p ∈ C) (hpK : p.1 < K) :
    bidEnvelope C p.1 ≤ p.2 := by
  apply csSup_le (lowerBidSet_nonempty C p.1)
  rintro b (rfl | ⟨q,hq,hqp,rfl⟩)
  · exact hnonneg p hp
  · exact hsort q hq (hqp.trans hpK) p hp hqp

theorem used_le_bidEnvelope_right {C : Set (ℝ × ℝ)} {U : ℝ}
    (hU : 0 ≤ U) (hbound : ∀ p ∈ C, p.2 ≤ U)
    {p : ℝ × ℝ} (hp : p ∈ C) {w : ℝ} (hpw : p.1 < w) :
    p.2 ≤ bidEnvelope C w :=
  le_csSup (lowerBidSet_bddAbove hU hbound w) (Or.inr ⟨p,hp,hpw,rfl⟩)

theorem used_bid_eq_envelope_at_continuity {C : Set (ℝ × ℝ)} {U K : ℝ}
    (hU : 0 ≤ U) (hbound : ∀ p ∈ C, p.2 ≤ U)
    (hnonneg : ∀ p ∈ C, 0 ≤ p.2)
    (hsort : ∀ p ∈ C, p.1 < K → ∀ q ∈ C, p.1 < q.1 → p.2 ≤ q.2)
    {p : ℝ × ℝ} (hp : p ∈ C) (hpK : p.1 < K)
    (hc : ContinuousAt (bidEnvelope C) p.1) : p.2=bidEnvelope C p.1 := by
  apply le_antisymm
  · have ht : Tendsto (fun n : ℕ => p.1+1/((n:ℝ)+1)) atTop (𝓝 p.1) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add p.1
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hc.tendsto.comp ht)
      (Eventually.of_forall fun n => used_le_bidEnvelope_right hU hbound hp
        (by have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
            exact lt_add_of_pos_right _ (div_pos (by norm_num) hn)))
  · exact bidEnvelope_le_used hnonneg hsort hp hpK

theorem source_avoids_countable_values (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {N : Set ℝ} (hN : N.Countable) : ∀ᵐ p ∂G, p.1 ∉ N := by
  have he : {p : ℝ × ℝ | p.1 ∈ N}=⋃ v ∈ N, {p : ℝ × ℝ | p.1=v} := by
    ext p
    simp
  have hn : G {p : ℝ × ℝ | p.1 ∈ N}=0 := by
    rw [he]
    exact (measure_biUnion_null_iff hN).mpr
      (fun v _ => source_value_level_null i G hvalue v)
  exact measure_eq_zero_iff_ae_notMem.mp hn

theorem source_exists_monotone_pure_bid (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U))
    (hIC : ∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U),
      payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
        payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) :
    ∃ B : ℝ → ℝ, Monotone B ∧ Measurable B ∧ (∀ v, B v ∈ Icc (0:ℝ) U) ∧
      ∀ᵐ p ∂G, p.1 < K →
        p.2=B p.1 ∧ sourceRank (cutoff i) (G.map Prod.snd) (B p.1)=p.1 := by
  let C := usedSet i m G g margin U
  have hC := usedSet_full i m G hvalue hatom g margin U hmenu hIC
  have hb : ∀ p ∈ C, p.2 ≤ U := fun p hp => hp.2.2.1.2.trans (min_le_right _ _)
  have h0 : ∀ p ∈ C, 0 ≤ p.2 := fun p hp => hp.2.1.le
  have hs := usedSet_sorted i hm G (hmenu.mono fun _ hp => hp.1) hatom g hg margin U
  have hmono := bidEnvelope_monotone hU hb
  have hct := source_avoids_countable_values i G hvalue
    hmono.countable_not_continuousAt
  have hr := source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin U hC
  refine ⟨bidEnvelope C,hmono,hmono.measurable,fun v => bidEnvelope_bounds hU hb v,?_⟩
  filter_upwards [hC,hct] with p hp hc hpK
  have hc' : ContinuousAt (bidEnvelope C) p.1 := by
    simpa only [mem_setOf_eq,not_not] using hc
  have he := used_bid_eq_envelope_at_continuity hU hb h0 hs hp hpK hc'
  exact ⟨he,by rw [← he]; exact hr p hp hpK⟩

end FCAppendix.Affine.Uniform06.LiteralPureBid
