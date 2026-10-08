import FCAppendix.Ample.RouteIdentificationTierLaw
import FCAppendix.Ample.BoundaryActualContact
import FCAppendix.Ample.BoundaryRankAlgebra

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

namespace RouteIdentificationDetails
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma actual_failure_shortage (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (a : JointAction n) (hb : 0 < a.bid) :
    actualFailure Γ a = Shortage.congestionProb (visibleLaw Γ a.bid)
      (m-1) c (selected n a.routeCount) := by
  rw [actualFailure_eq_congestProb Γ hm hA hatom hj a hb,
    Shortage.congestionProb_eq_simultaneous, visibleLaw_eq_contactLaw,
    contactLaw_congestionProb]
  rfl

lemma allMass_ge_mass (μ : FiniteLaw (Finset (Fin n))) (S : Finset (Fin n)) :
    μ.mass S ≤ Shortage.allMass μ S := by
  classical
  have hs : μ.prob (fun T => T=S) = μ.mass S := by
    rw [FiniteLaw.prob_eq_expect, μ.expect_singleton]
  rw [← hs]
  exact μ.prob_mono (fun T hT => by subst T; exact subset_rfl)

lemma visible_selected_mass (Γ : FiniteGame m n c Seed) (b : ℝ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    (visibleLaw Γ b).mass (selected n k) = visibleClassMass Γ b k / (n.choose k : ℝ) := by
  have hkn := (Finset.mem_Icc.mp hk).2
  have hSne : selected n k ≠ ∅ := by
    intro he
    have hh := card_selected hkn
    rw [he, Finset.card_empty] at hh
    have := (Finset.mem_Icc.mp hk).1
    omega
  rw [visibleLaw_eq_contactLaw, contactLaw_mass, contactWeight_of_ne _ hSne, card_selected hkn]

lemma contactLaw_prefix_allMass {pi : ℕ → ℝ} {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (hpref : ValidLaw n (prefixLaw pi k)) :
    Shortage.allMass (contactLaw n (prefixLaw pi k) hpref) (selected n k) =
      pi k / (n.choose k : ℝ) := by
  classical
  let S := selected n k
  have hSc : S.card = k := card_selected (Finset.mem_Icc.mp hk).2
  have hS : S ≠ ∅ := by
    intro he
    rw [he, Finset.card_empty] at hSc
    have := (Finset.mem_Icc.mp hk).1
    omega
  rw [Shortage.allMass, FiniteLaw.prob_eq_expect]
  change (∑ T : Finset (Fin n), contactWeight n (prefixLaw pi k) T *
    (if S ⊆ T then (1 : ℝ) else 0)) = _
  rw [Finset.sum_eq_single S]
  · rw [if_pos (subset_rfl), mul_one, contactWeight_of_ne _ hS, hSc]
    simp only [prefixLaw, le_refl, if_true]
  · intro T _ hTS
    by_cases hST : S ⊆ T
    · have hkT : k < T.card := by
        have hc := Finset.card_le_card hST
        rw [hSc] at hc
        apply lt_of_le_of_ne hc
        intro he
        have heq : S = T := Finset.eq_of_subset_of_card_le hST (by omega)
        exact hTS heq.symm
      have hT : T ≠ ∅ := by
        intro he; rw [he, Finset.card_empty] at hkT; omega
      simp only [hST, if_true, mul_one, contactWeight_of_ne _ hT, prefixLaw,
        not_le.mpr hkT, if_false, zero_div]
    · simp only [hST, if_false, mul_zero]
  · intro hSnot
    exact False.elim (hSnot (Finset.mem_univ S))

lemma finite_allContact_eq_rank_prefix {pi : ℕ → ℝ} {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (hpref : ValidLaw n (prefixLaw pi k))
    (nu : ℕ → Measure ℝ) (h u : ℝ)
    (htails : ∀ j ∈ Finset.Icc 1 n, (nu j).real (Ioc u h) = if j ≤ k then pi j else 0) :
    Shortage.allMass (contactLaw n (prefixLaw pi k) hpref) (selected n k) =
      Ample.CompletionDraft.allContactTail n k nu h u := by
  rw [contactLaw_prefix_allMass hk hpref,
    Ample.CompletionDraft.allContactTail_at_prefix hk pi nu h u htails]

lemma visible_prefix_allMass_tendsto {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (bid : ℕ → ℝ)
    {pi : ℕ → ℝ} {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hpref : ValidLaw n (prefixLaw pi k))
    (hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => visibleClassMass (Γ t) (bid t) j) atTop (𝓝 (prefixLaw pi k j))) :
    Tendsto (fun t => Shortage.allMass (visibleLaw (Γ t) (bid t)) (selected n k))
      atTop (𝓝 (pi k/(n.choose k : ℝ))) := by
  classical
  have hm (T : Finset (Fin n)) : Tendsto
      (fun t => (visibleLaw (Γ t) (bid t)).mass T) atTop
      (𝓝 ((contactLaw n (prefixLaw pi k) hpref).mass T)) := by
    simp_rw [visibleLaw_eq_contactLaw]
    exact contactLaw_mass_tendsto (fun t => visibleClassMass_valid (Γ t) (bid t)) hpref hconv T
  have hh := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n)))
    (fun T _ => (hm T).mul_const (if selected n k ⊆ T then (1 : ℝ) else 0))
  rw [← contactLaw_prefix_allMass hk hpref]
  simpa only [Shortage.allMass, FiniteLaw.prob_eq_expect, FiniteLaw.expect] using hh

lemma positive_class_all_failure_lower (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hc : c ≤ m-1) (hA : Γ.A = Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (ha : NonpositiveAbstention Γ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {q : ℝ} (hq : 0 < q)
    (hqm : q < positiveRouteMass Γ (fun j => j=k)) :
    (q/(n.choose k : ℝ))^(m-1) ≤ actualAllFailure Γ := by
  classical
  let i : Fin m := ⟨0, hm⟩
  obtain ⟨hi, hqhi, hhim⟩ := exists_between hqm
  have hgood : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (problem Γ i).BestResponse x.1 x.2 ∧ (x.1 ≤ Γ.g → x.2.routeCount = 0) :=
    (ae_bestResponse_compProd Γ hu i).and ha
  obtain ⟨x, hxc, hxl, _, _, hxg⟩ :=
    (positiveBidStratum Γ hatom (fun j => j=k)).exists_good_in_band
      ((measurable_bid n).comp measurable_snd) hq hqhi hhim ∅
      (by simp only [measureReal_empty]; linarith) _ hgood
  have hxk : x.2.routeCount = k := hxc.2.2
  have hv : 0 < x.1-Γ.g := by
    by_contra hvn
    have hzero := hxg.2 (by linarith)
    have hpos := hxc.2.1
    omega
  have hbr : (problem Γ i).BestResponse ((x.1-Γ.g)+Γ.g) x.2 := by
    simpa only [sub_add_cancel] using hxg.1
  have hn : 0 < n := by have := Finset.mem_Icc.mp hk; omega
  have hAM1 := (actual_AM1 Γ hm hA hf hatom hj hn hv x.2 hbr).2.1
  have htail : q ≤ visibleClassMass Γ x.2.bid k := by
    rw [← positiveRouteTail_class_eq Γ x.2.bid hxc.1.le (Finset.mem_Icc.mp hk).1]
    simpa only [positiveBidStratum_tail] using hxl
  have hD : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (Finset.mem_Icc.mp hk).2
  have hbase : q/(n.choose k : ℝ) ≤ Shortage.allMass (visibleLaw Γ x.2.bid) (selected n k) := by
    calc
      q/(n.choose k : ℝ) ≤ visibleClassMass Γ x.2.bid k/(n.choose k : ℝ) :=
        div_le_div_of_nonneg_right htail hD.le
      _ = (visibleLaw Γ x.2.bid).mass (selected n k) := (visible_selected_mass Γ x.2.bid hk).symm
      _ ≤ _ := allMass_ge_mass _ _
  have hpow := pow_le_pow_left₀ (div_pos hq hD).le hbase (m-1)
  have hlow := (Shortage.finite_sandwich (visibleLaw Γ x.2.bid) (m-1) c hc (selected n k)).1
  have heq := actual_failure_shortage Γ hm hA hatom hj x.2 hxc.1
  rw [hxk] at heq
  have hupp : Shortage.congestionProb (visibleLaw Γ x.2.bid) (m-1) c
      (selected n k) ≤ actualAllFailure Γ := by
    rw [← heq]
    exact hAM1
  exact hpow.trans (hlow.trans hupp)

end RouteIdentificationDetails

end FCAppendix.Bayes
