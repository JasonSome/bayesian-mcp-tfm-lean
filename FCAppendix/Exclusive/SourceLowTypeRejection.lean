import FCAppendix.Exclusive.SourceLowTypeSmallBid
import FCAppendix.Exclusive.SourceLowTypePayoff

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem focalList_positives (i : Fin m) (d : UserProfile m n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : HighRivals a i d) :
    Marker.positives (focalList i b d) = insert i (activeRivals i d) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [Marker.positives,focalList,hb]
  · rcases hd j hji with hz | ⟨_,hfloor⟩
    · simp [Marker.positives,focalList,hji,hz,activeRivals]
    · by_cases hk : (d j).1.2.routeCount = 0
      · simp [Marker.positives,focalList,hji,hk,activeRivals]
      · have hp := ha.trans_le hfloor
        simp [Marker.positives,focalList,hji,hk,hp,activeRivals]

theorem focalList_lows_singleton (cutoff : ℝ) (i : Fin m) (d : UserProfile m n)
    {a b : ℝ} (hb : 0 < b) (hbid : b < cutoff) (hcut : cutoff ≤ a)
    (hd : HighRivals a i d) : Marker.lows cutoff (focalList i b d) = {i} := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [Marker.lows,focalList,hb,hbid]
  · rcases hd j hji with hz | ⟨_,hfloor⟩
    · simp [Marker.lows,focalList,hji,hz]
    · by_cases hk : (d j).1.2.routeCount = 0
      · simp [Marker.lows,focalList,hji,hk]
      · have hnot : ¬ (d j).1.2.bid < cutoff := not_lt_of_ge (hcut.trans hfloor)
        simp [Marker.lows,focalList,hji,hk,hnot]

theorem focalList_lows_zero (cutoff : ℝ) (i : Fin m) (d : UserProfile m n)
    {a : ℝ} (hcut : cutoff ≤ a) (hd : HighRivals a i d) :
    Marker.lows cutoff (focalList i 0 d) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  by_cases hji : j = i
  · simp [focalList,hji] at hh
  · rcases hd j hji with hz | ⟨_,hfloor⟩
    · simp [focalList,hji,hz] at hh
    · by_cases hk : (d j).1.2.routeCount = 0
      · simp [focalList,hji,hk] at hh
      · simp only [focalList,if_neg hji,if_neg hk,Option.getD_some] at hh
        exact (not_lt_of_ge (hcut.trans hfloor)) hh.2

theorem focalList_zeros (i : Fin m) (d : UserProfile m n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : HighRivals a i d) :
    Marker.zeros (focalList i b d) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  by_cases hji : j = i
  · simp [focalList,hji,ne_of_gt hb] at hh
  · rcases hd j hji with hz | ⟨_,hfloor⟩
    · simp [focalList,hji,hz] at hh
    · by_cases hk : (d j).1.2.routeCount = 0
      · simp [focalList,hji,hk] at hh
      · have hp := ha.trans_le hfloor
        simp [focalList,hji,hk,ne_of_gt hp] at hh

theorem focalList_distinct (i : Fin m) (d : UserProfile m n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hbid : b < a) (hd : HighRivals a i d)
    (hdist : Set.InjOn (fun j => (d j).1.2.bid) (activeRivals i d)) :
    Set.InjOn (fun j => (focalList i b d j).getD 0)
      (Marker.positives (focalList i b d)) := by
  classical
  rw [focalList_positives i d ha hb hd]
  intro j hj l hl he
  by_cases hji : j = i
  · subst j
    by_cases hli : l = i
    · exact hli.symm
    · have hla : l ∈ activeRivals i d := (Finset.mem_insert.mp hl).resolve_left hli
      have hkl := ((mem_activeRivals i l d).mp hla).2
      have hfloor : a ≤ (d l).1.2.bid := by
        rcases hd l hli with hz | ⟨_,hh⟩
        · exact (hkl hz).elim
        · exact hh
      simp only [focalList,if_true,if_neg hli,if_neg hkl,Option.getD_some] at he
      exact False.elim (by linarith)
  · by_cases hli : l = i
    · subst l
      have hja : j ∈ activeRivals i d := (Finset.mem_insert.mp hj).resolve_left hji
      have hkj := ((mem_activeRivals i j d).mp hja).2
      have hfloor : a ≤ (d j).1.2.bid := by
        rcases hd j hji with hz | ⟨_,hh⟩
        · exact (hkj hz).elim
        · exact hh
      simp only [focalList,if_true,if_neg hji,if_neg hkj,Option.getD_some] at he
      exact False.elim (by linarith)
    · have hja : j ∈ activeRivals i d := (Finset.mem_insert.mp hj).resolve_left hji
      have hla : l ∈ activeRivals i d := (Finset.mem_insert.mp hl).resolve_left hli
      have hkj := ((mem_activeRivals i j d).mp hja).2
      have hkl := ((mem_activeRivals i l d).mp hla).2
      apply hdist hja hla
      simpa only [focalList,if_neg hji,if_neg hli,if_neg hkj,if_neg hkl,Option.getD_some] using he

theorem source_symmetric (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (j : Fin n) (ℓ : LocalList m) : SymmetricAtList Γ ℓ (seedLottery Γ j ℓ) := by
  intro l
  have he : (fun s => (Γ.policy l ℓ s).val) = fun s => (Γ.policy j ℓ s).val := by
    funext s
    rw [hpolicy,hpolicy]
  unfold seedLottery
  congr 1

theorem binomialPolynomial_zero (k : ℕ) (f : ℕ → ℝ) :
    Narrow.binomialPolynomial k f 0 = f 0 := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp [Narrow.binomialPolynomial,ih]

theorem source_actual_small_bid_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (tariff : UserTariff) (i : Fin m) {a : ℝ} (ha : 0 < a)
    (hcut : cutoff ≤ a) (hthreshold : cutoff ≤ a*(1-1/(n:ℝ))^(n-1))
    (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals a i d ∧
      Set.InjOn (fun j => (d j).1.2.bid) (activeRivals i d))
    (v : ℝ) (act : JointAction n) (hb : act.bid < cutoff) :
    exclusiveTariffPayoff Γ tariff i v act = 0 := by
  classical
  let j : Fin n := ⟨0,by omega⟩
  rw [exclusiveTariffPayoff_eq_test,interim_expect_eq_profile_update Γ i (v,act)]
  have he (τ : Equiv.Perm (Fin n)) :
      (∫ d, (profileCountLaw Γ (Function.update d i ((v,act),τ)) i).expect
        (fun r => payoffTest tariff Γ.G Γ.g v act.bid r.val) ∂userProfileLaw Γ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hd] with d hd
    let ℓ := focalList i act.bid d
    have hmarg : Proposer.marginal (seedLottery Γ j ℓ) i = 0 := by
      by_cases hb0 : act.bid = 0
      · have hs := source_symmetric_canonical Γ hm hn hc cutoff fallback hfallback hcanonical
          hpolicy ℓ (by simpa only [ℓ,hb0] using focalList_lows_zero cutoff i d hcut hd.1)
        rw [hs j,canonicalLottery_marginal]
        apply canonicalMarginal_nonpositive n hn c (listBids ℓ) i
        simp [ℓ,listBids,focalList,readBid,hb0]
      · have hbpos : 0 < act.bid := lt_of_le_of_ne act.bid_nonneg (Ne.symm hb0)
        apply source_low_marginal_zero Γ hm hn hc cutoff fallback hfallback hcanonical hpolicy
          j ℓ i ha hbpos (by simp [ℓ,listBids,focalList,readBid])
          (focalList_lows_singleton cutoff i d hbpos hb hcut hd.1)
          (focalList_zeros i d ha hbpos hd.1)
          (focalList_distinct i d ha hbpos (hb.trans_le hcut) hd.1 hd.2) ?_ hthreshold hb
        intro l hl hli
        have hla : l ∈ activeRivals i d :=
          (Finset.mem_insert.mp ((focalList_positives i d ha hbpos hd.1) ▸ hl)).resolve_left hli
        have hk := ((mem_activeRivals i l d).mp hla).2
        rcases hd.1 l hli with hz | ⟨_,hfloor⟩
        · exact (hk hz).elim
        · simpa [ℓ,listBids,focalList,readBid,hli,hk] using hfloor
    have htest := profile_test_of_recipient_common_list Γ (Function.update d i ((v,act),τ))
      i ℓ (observe_update_recipient_eq_focalList a i d hd.1 (v,act) τ)
      (seedLottery Γ j ℓ) (source_symmetric Γ hm hn hc cutoff fallback hpolicy j ℓ)
      (payoffTest tariff Γ.G Γ.g v act.bid)
    rw [hmarg,binomialPolynomial_zero] at htest
    simpa [payoffTest,successIndicator,UserTariff.charge_zero,Γ.G.zero] using htest
  simp_rw [he]
  simp

end FCAppendix.Bayes.ExclusiveSource
