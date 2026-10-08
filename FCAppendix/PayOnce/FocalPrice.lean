import FCAppendix.PayOnce.ProfilePrice

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set CommonList Bayes KernelTailEvent
open scoped BigOperators
variable {N n c : ℕ}

noncomputable def focalPrice (n c : ℕ) (hn : 2 ≤ n) (b : ℝ) (r : Fin N → ℝ) : ℝ :=
  profilePrice n c hn (Nat.succ_pos N) (Fin.cons b r)

theorem measurable_focalPrice_joint (hn : 2 ≤ n) :
    Measurable (fun z : ℝ × (Fin N → ℝ) => focalPrice n c hn z.1 z.2) := by
  apply (measurable_profilePrice hn (Nat.succ_pos N)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_focalPrice (hn : 2 ≤ n) (b : ℝ) :
    Measurable (focalPrice (N := N) n c hn b) := by
  unfold focalPrice
  apply (measurable_profilePrice (c := c) hn (Nat.succ_pos N)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact measurable_pi_apply j

theorem active_card_cons (b : ℝ) (r : Fin N → ℝ) (hb : 0 < b) :
    Fintype.card (Active (Fin.cons b r)) = Fintype.card (Active r)+1 := by
  classical
  have hcard (Q : ℕ) (s : Fin Q → ℝ) :
      (Fintype.card (Active s):ℝ) = ∑ j, if 0 < s j then (1:ℝ) else 0 := by
    simp [Active,Fintype.card_subtype]
  have hh : (Fintype.card (Active (Fin.cons b r)):ℝ) = (Fintype.card (Active r):ℝ)+1 := by
    rw [hcard (N+1),hcard N,Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,if_pos hb]
    ring
  exact_mod_cast hh

theorem focalPrice_spec (hn : 2 ≤ n) (b : ℝ) (r : Fin N → ℝ) (hb : 0 < b) :
    0 < focalPrice n c hn b r ∧
      kernel n b (focalPrice n c hn b r) + ∑ i, kernel n (r i) (focalPrice n c hn b r) =
        min c (Fintype.card (Active r)+1) ∧
      allocation n c hn r b = kernel n b (focalPrice n c hn b r) := by
  have hp := profilePrice_spec (c := c) hn (Nat.succ_pos N) (Fin.cons b r)
  have hroot : kernel n b (focalPrice n c hn b r) +
      ∑ i, kernel n (r i) (focalPrice n c hn b r) = min c (Fintype.card (Active r)+1) := by
    simpa only [focalPrice,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,active_card_cons b r hb] using hp.2.2
  exact ⟨hp.1,hroot,allocation_eq_kernel hn r hb hp.1 hroot⟩

theorem rival_sum_le_of_focalPrice_le (hn : 2 ≤ n) (b : ℝ) (r : Fin N → ℝ) (hb : 0 < b)
    {T : ℝ} (hT : 0 < T) (hprice : focalPrice n c hn b r ≤ T) :
    (∑ i, kernel n (r i) T) ≤ (c:ℝ) := by
  obtain ⟨hL,hcap,_⟩ := focalPrice_spec (c := c) hn b r hb
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    kernel_antitone_price hn hL hT hprice (b := r i))
  have hb0 := (KernelTailEvent.kernel_bounds hn hL b).1
  have hc : ((min c (Fintype.card (Active r)+1):ℕ):ℝ) ≤ c :=
    Nat.cast_le.mpr (min_le_left _ _)
  linarith

theorem focalPrice_lt_of_rival_sum_le (hn : 2 ≤ n) (b : ℝ) (r : Fin N → ℝ) (hb : 0 < b)
    {T : ℝ} (hT : 0 < T) (hactive : c ≤ Fintype.card (Active r)+1)
    (hsmall : (∑ i, kernel n (r i) T) ≤ (c:ℝ)-2) : focalPrice n c hn b r < T := by
  obtain ⟨hL,hcap,_⟩ := focalPrice_spec (c := c) hn b r hb
  rw [min_eq_left hactive] at hcap
  by_contra h
  have hTL : T ≤ focalPrice n c hn b r := le_of_not_gt h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    kernel_antitone_price hn hT hL hTL (b := r i))
  have hbf := (KernelTailEvent.kernel_bounds hn hL b).2
  linarith

theorem focalPrice_event_sandwich (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b)
    {T : ℝ} (hT : 0 < T) :
    {r : Fin N → ℝ | (∑ i, kernel n (r i) T) ≤ (c:ℝ)-2} \
        {r | Fintype.card (Active r)+1 < c} ⊆
      {r | focalPrice n c hn b r ≤ T} ∧
    {r : Fin N → ℝ | focalPrice n c hn b r ≤ T} ⊆
      {r | (∑ i, kernel n (r i) T) ≤ (c:ℝ)} := by
  constructor
  · intro r hr
    exact (focalPrice_lt_of_rival_sum_le hn b r hb hT (Nat.le_of_not_gt hr.2) hr.1).le
  · intro r hr
    exact rival_sum_le_of_focalPrice_le hn b r hb hT hr

end FCAppendix.PayOnce.DummyKernel
