import FCAppendix.Affine.Uniform06.FixedPriceRawDerivative
import FCAppendix.Affine.Uniform06.EntryLiteralResponseMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceEntryGeometry

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelIdentity EntryLiteralResponseGeometry
open ActualEntryGoodGeometry ReciprocalSecantBounds FixedPriceRawDerivative
open EntryRawCentral EntrySamplingLaw

variable {N C : ℕ}

theorem supported_path_regularity (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (r : Fin N → RowRival) (hno : ∀ j,(r j).1 ≠ 1)
    (hcap : ∀ j,(r j).1=0 → (r j).2 ≤ U)
    (hgood : r ∈ RivalGood.good μ (tests (xi i) g A U) N ε)
    (path : Path (Fin (N+1)) (imbalance (patternTemplate C (fun j => (r j).1))))
    (hpath : 0 < (pathLaw (weights (xi i) g (patternTemplate C (fun j => (r j).1))
      (rowBids b r)) (imbalance (patternTemplate C (fun j => (r j).1))) ∅).mass path) :
    let E := finalSet (imbalance (patternTemplate C (fun j => (r j).1))) ∅ path
    (0:Fin (N+1)) ∉ E ∧
      complementMarginal (xi i) (patternTemplate C (fun j => (r j).1)) (rowBids b r) E 0 < 1 ∧
      ∃ j : Fin N,j.succ ∉ E ∧ (r j).1=0 ∧ b<(r j).2 ∧ (1-xi i)*(r j).2≤ b := by
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hc := finite_counts μ i g h r hno hgood
  have hs := all_action_guard_and_strip μ g h.rivals_pos hξ hξ1 h.epsilon_nonneg
    h.prefix.margin_pos h.prefix.population_pos h.prefix.lower_pos
    (by linarith [h.prefix.lower_pos,h.radius_pos]) h.prefix.rejectionScale_pos
    h.means h.floor_error h.residual_positive h.residual_room h.demand_margin
    h.weight_margin h.rejection_margin h.seed_margin h.strip_margin h.count_margin r hno hgood
  let T := patternTemplate C (fun j => (r j).1)
  let E := finalSet (imbalance T) ∅ path
  have hα : 0 < guardAlpha (xi i) g T (rowBids b r) := by rw [hs.2.1 b]; norm_num
  have hf := all_action_focal_not_sampled hξ g h.prefix T (rowBids b r) 0
    h.bid_window.2 hα path hpath
  have hBU : ∀ j,rowBids b r j ≤ U := by
    intro j
    refine Fin.cases h.bid_cap (fun j => ?_) j
    by_cases ht : (r j).1=0
    · simpa [rowBids,ht] using hcap j ht
    · simp [rowBids,ht,h.cap_pos.le]
  have hresponse := EntryLiteralCentral.literal_response_from_guards i g hb h.cap_pos
    h.prefix.margin_pos h.prefix.population_pos h.radius_pos h.prefix.lower_pos h.cap_receipt
    r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hBU h.half_receipt hα path hpath hf
  obtain ⟨Λ,hΛ,hroot,hR⟩ := all_action_roots_and_reciprocals g hξ hξ1 h.cap_pos
    h.prefix.margin_pos h.prefix.population_pos h.radius_pos h.prefix.lower_pos h.cap_receipt
    h.strip_above r hcap hs.2.1 hs.2.2 b h.bid_window h.bid_cap path hpath
  have hRpos : 0 < reciprocalSum (rowBids b r) (insert 0 E) b := by
    have hNr : (0:ℝ)< N := by exact_mod_cast h.rivals_pos
    exact (div_pos (mul_pos h.strip_pos hNr) (mul_pos (by norm_num) h.cap_pos)).trans_le
      (hR b h.bid_window)
  have hp1 : complementMarginal (xi i) T (rowBids b r) E 0 < 1 := by
    have hbounds := LiteralPrefixStieltjes.complement_bounds hξ hξ1 T (rowBids b r) E 0
    by_cases hp : 0 < complementMarginal (xi i) T (rowBids b r) E 0
    · have hprice := (hresponse.2.2 hp).1
      have hκb : (1-xi i)*b ≤ g.multiplier-g.radius :=
        (mul_le_mul_of_nonneg_left h.bid_cap (sub_pos.mpr hξ1).le).trans h.cap_receipt
      dsimp only [LiteralKernelIdentity.focalPrice] at hprice
      change g.multiplier-g.radius < b*(1-xi i*complementMarginal (xi i) T (rowBids b r) E 0)
        at hprice
      nlinarith [mul_pos hb hξ]
    · linarith
  refine ⟨hf,hp1,?_⟩
  unfold reciprocalSum at hRpos
  obtain ⟨k,_,hk⟩ := Finset.exists_lt_of_sum_lt (f := fun _ : Fin (N+1) => (0:ℝ))
    (by simpa only [Finset.sum_const_zero] using hRpos)
  have hke : k ∉ insert (0:Fin (N+1)) E := by
    intro he
    simp only [if_pos he] at hk
    exact lt_irrefl _ hk
  have hkb : b < rowBids b r k := by
    by_contra hnot
    simp only [if_neg hke,reciprocalTerm,if_neg hnot] at hk
    exact lt_irrefl _ hk
  have hk0 : k ≠ (0:Fin (N+1)) := fun he => hke (he ▸ Finset.mem_insert_self _ _)
  revert hke hkb hk0
  refine Fin.cases (fun _ _ hk0 => (hk0 rfl).elim) (fun j hje hjb _ => ?_) k
  have ht : (r j).1=0 := by
    by_contra hn
    simp only [rowBids,Fin.cons_succ,if_neg hn] at hjb
    linarith
  have hjb' : b<(r j).2 := by simpa [rowBids,ht] using hjb
  have hjE : j.succ ∉ E := fun he => hje (Finset.mem_insert_of_mem he)
  exact ⟨j,hjE,ht,hjb',
    (mul_le_mul_of_nonneg_left (hcap j ht) (sub_pos.mpr hξ1).le).trans
      (h.cap_receipt.trans h.bid_window.1)⟩

theorem usable_regularity (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) (hx : x ∈ usable μ i g b A U ε) :
    (0:Fin (N+1)) ∉ sampleSet i g b x ∧ complement i C g b x < 1 ∧
      ∃ j : Fin N,j.succ ∉ sampleSet i g b x ∧ (x.1 j).1=0 ∧
        b<(x.1 j).2 ∧ (1-xi i)*(x.1 j).2≤ b := by
  have hc := finite_counts μ i g h x.1 hx.2.1 hx.1
  have hd := RawDeficitGeometry.template_imbalance_eq_draws C x.1
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hw : weights (xi i) g (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) =
      profile i g b x.1 := EntryLiteralCentral.weights_eq_profile i g h.requiredDemand_eq C b x.1
  have hh : ∀ (d : ℕ) (he : imbalance (patternTemplate C (fun j => (x.1 j).1))=d)
      (p : Path (Fin (N+1)) d), 0 < (pathLaw (profile i g b x.1) d ∅).mass p →
      (0:Fin (N+1)) ∉ finalSet d ∅ p ∧
        complementMarginal (xi i) (patternTemplate C (fun j => (x.1 j).1))
          (rowBids b x.1) (finalSet d ∅ p) 0 < 1 ∧
        ∃ j : Fin N,j.succ ∉ finalSet d ∅ p ∧ (x.1 j).1=0 ∧
          b<(x.1 j).2 ∧ (1-xi i)*(x.1 j).2≤ b := by
    intro d he p hp
    subst d
    rw [← hw] at hp
    exact supported_path_regularity μ i g h x.1 hx.2.1 hx.2.2.1 hx.1 p hp
  exact hh _ hd _ hx.2.2.2

theorem actual_fixed_bid_derivative (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s) :
    ∀ᵐ x ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N,
      x ∈ usable (RawMixedSource.source i G) i g b A U ε →
        HasDerivAt (fun a => complementMarginal (xi i)
          (patternTemplate C (fun j => (x.1 j).1)) (rowBids a x.1) (sampleSet i g b x) 0)
          (MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (x.1 j).1))
            (rowBids 0 x.1) (sampleSet i g b x) 0 b) b := by
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hr := original_all_removed_derivatives (N := N) i G hnull hnon hb
  have hx := (measurePreserving_fst (μ := Measure.pi (fun _ : Fin N => RawMixedSource.source i G))
    (ν := (volume : Measure unitInterval))).quasiMeasurePreserving.ae hr
  filter_upwards [hx] with x hx huse
  have hg := usable_regularity (RawMixedSource.source i G) i g h x huse
  exact hx C (sampleSet i g b x) hg.1 hg.2.1 hg.2.2

end FCAppendix.Affine.Uniform06.FixedPriceEntryGeometry
