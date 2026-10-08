import FCAppendix.Finite.PPISubcutoffPairGame

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

private theorem card_sub_success_le_ordered_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    (S.card:ℝ)-successIndicator S.card ≤
      ∑ j : ι, ∑ l : ι, if j ≠ l ∧ j ∈ S ∧ l ∈ S then (1:ℝ) else 0 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨l,hl⟩ := hS
    have hcard : 0 < S.card := Finset.card_pos.mpr ⟨l,hl⟩
    have hsum : (∑ j : ι, if j ∈ S.erase l then (1:ℝ) else 0) = (S.card:ℝ)-1 := by
      simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [Finset.card_erase_of_mem hl,Nat.cast_sub hcard,Nat.cast_one]
    rw [successIndicator,if_neg (Nat.ne_of_gt hcard),← hsum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ S.erase l
    · rw [if_pos hj]
      have hm : j ≠ l ∧ j ∈ S := Finset.mem_erase.mp hj
      have hs := Finset.single_le_sum
        (f := fun l' : ι => if j ≠ l' ∧ j ∈ S ∧ l' ∈ S then (1:ℝ) else 0)
        (fun l' _ => by split_ifs <;> norm_num) (Finset.mem_univ l)
      have hpair : j ≠ l ∧ j ∈ S ∧ l ∈ S := ⟨hm.1,hm.2,hl⟩
      simpa only [if_pos hpair] using hs
    · rw [if_neg hj]
      exact Finset.sum_nonneg (fun l' _ => by split_ifs <;> norm_num)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [successIndicator]

def ppiPairFlag (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (b : ℝ) (j l : Fin n) (ω : Sample (N+1) n Seed) : ℝ := by
  classical
  exact if j ≠ l ∧ Accepts Γ i b j ω.1 ∧ Accepts Γ i b l ω.1 then 1 else 0

lemma ppiPairFlag_nonneg (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (b : ℝ) (j l : Fin n) (ω : Sample (N+1) n Seed) :
    0 ≤ ppiPairFlag Γ i b j l ω := by
  unfold ppiPairFlag
  split_ifs <;> norm_num

lemma integrable_ppiPairFlag (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (b : ℝ) (j l : Fin n) : Integrable (ppiPairFlag Γ i b j l) (sampleLaw Γ) := by
  classical
  by_cases hjl : j = l
  · have hz : ppiPairFlag Γ i b j l = fun _ => 0 := by
      funext ω
      simp [ppiPairFlag,hjl]
    rw [hz]
    exact integrable_zero _ _ _
  · have hE : MeasurableSet {ω : Sample (N+1) n Seed |
        Accepts Γ i b j ω.1 ∧ Accepts Γ i b l ω.1} :=
      measurable_fst ((measurableSet_accepts Γ i b j).inter
        (measurableSet_accepts Γ i b l))
    have hh := (integrable_const (1:ℝ) : Integrable
      (fun _ : Sample (N+1) n Seed => (1:ℝ)) (sampleLaw Γ)).indicator hE
    have heq : ppiPairFlag Γ i b j l =
        {ω : Sample (N+1) n Seed | Accepts Γ i b j ω.1 ∧ Accepts Γ i b l ω.1}.indicator
          (fun _ => (1:ℝ)) := by
      funext ω
      simp [ppiPairFlag,Set.indicator,hjl]
    rw [heq]
    exact hh

lemma integral_ppiPairFlag (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (b : ℝ) (j l : Fin n) :
    ∫ ω, ppiPairFlag Γ i b j l ω ∂sampleLaw Γ =
      if j = l then 0 else ppiPairProb Γ i b j l := by
  classical
  by_cases hjl : j = l
  · simp [ppiPairFlag,hjl]
  · rw [if_neg hjl]
    let E : Set (Background (N+1) n Seed) :=
      {ω | Accepts Γ i b j ω ∧ Accepts Γ i b l ω}
    have hE : MeasurableSet E := (measurableSet_accepts Γ i b j).inter
      (measurableSet_accepts Γ i b l)
    have hflag : ppiPairFlag Γ i b j l =
        (E ×ˢ (univ : Set (Equiv.Perm (Fin n)))).indicator (fun _ => (1:ℝ)) := by
      funext ω
      simp [ppiPairFlag,Set.indicator,hjl,E]
    have hEs : MeasurableSet (E ×ˢ (univ : Set (Equiv.Perm (Fin n)))) :=
      hE.prod MeasurableSet.univ
    rw [hflag]
    have hi := integral_indicator_const (μ := sampleLaw Γ) (1:ℝ) hEs
    simp only [smul_eq_mul,mul_one] at hi
    rw [hi]
    change ((backgroundLaw Γ).prod (permLaw n)).real (E ×ˢ univ) = _
    rw [measureReal_prod_prod,probReal_univ,mul_one]
    rfl

theorem ppi_duplicate_pointwise_le_pairs (Γ : FiniteGame (N+1) n c Seed)
    (i : Fin (N+1)) (act : JointAction n) (ω : Sample (N+1) n Seed) :
    ((focalCount Γ i act ω).val:ℝ)-successIndicator (focalCount Γ i act ω).val ≤
      ∑ j : Fin n, ∑ l : Fin n, ppiPairFlag Γ i act.bid j l ω := by
  classical
  let S := accepted (deviated i act ω) Γ.policy ω.1.2 i
  have h := card_sub_success_le_ordered_pairs S
  change (S.card:ℝ)-successIndicator S.card ≤ _
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro l _
  by_cases hjl : j ≠ l ∧ j ∈ S ∧ l ∈ S
  · have hj : Accepts Γ i act.bid j ω.1 :=
      ((mem_allocation_deviated_iff Γ i act ω j).mp
        ((Finset.mem_filter.mp hjl.2.1).2)).2
    have hl : Accepts Γ i act.bid l ω.1 :=
      ((mem_allocation_deviated_iff Γ i act ω l).mp
        ((Finset.mem_filter.mp hjl.2.2).2)).2
    have hpair : j ≠ l ∧ Accepts Γ i act.bid j ω.1 ∧ Accepts Γ i act.bid l ω.1 :=
      ⟨hjl.1,hj,hl⟩
    simp only [if_pos hjl,ppiPairFlag,if_pos hpair,le_refl]
  · rw [if_neg hjl]
    exact ppiPairFlag_nonneg Γ i act.bid j l ω

theorem ppi_duplicates_le_pair_sum (Γ : FiniteGame (N+1) n c Seed)
    (i : Fin (N+1)) (act : JointAction n) :
    ((problem Γ i).outcome act).duplicates ≤
      ∑ j : Fin n, ∑ l : Fin n, if j = l then 0 else ppiPairProb Γ i act.bid j l := by
  classical
  rw [problem_outcome,CountLaw.duplicates_eq_expect,CountLaw.expect_ofMeasure]
  have hInt (j : Fin n) : Integrable (fun ω => ∑ l : Fin n,
      ppiPairFlag Γ i act.bid j l ω) (sampleLaw Γ) :=
    integrable_finsetSum _ (fun l _ => integrable_ppiPairFlag Γ i act.bid j l)
  have h := integral_mono
    (CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i act)
      (measurable_focalCount Γ i act)
      (fun r => (r.val:ℝ)-successIndicator r.val))
    (integrable_finsetSum _ (fun j _ => hInt j))
    (ppi_duplicate_pointwise_le_pairs Γ i act)
  rw [integral_finsetSum _ (fun j _ => hInt j)] at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ => integrable_ppiPairFlag Γ i act.bid j l)]
  apply Finset.sum_congr rfl
  intro l _
  exact integral_ppiPairFlag Γ i act.bid j l

theorem ppi_duplicates_le_square_pair_bound (Γ : FiniteGame (N+1) n c Seed)
    (i : Fin (N+1)) (act : JointAction n) (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hpair : ∀ j l : Fin n, j ≠ l → ppiPairProb Γ i act.bid j l ≤ ε*q) :
    ((problem Γ i).outcome act).duplicates ≤ (n:ℝ)^2*ε*q := by
  classical
  have hh := ppi_duplicates_le_pair_sum Γ i act
  have hs : (∑ j : Fin n, ∑ l : Fin n,
      if j = l then 0 else ppiPairProb Γ i act.bid j l) ≤
        ∑ _j : Fin n, ∑ _l : Fin n, ε*q := by
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    by_cases hjl : j = l
    · simp only [if_pos hjl]
      exact mul_nonneg hε hq
    · simp only [if_neg hjl]
      exact hpair j l hjl
  apply hh.trans (hs.trans_eq _)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

def ppiAddRoute (act : JointAction n) (hk : act.routeCount < n) : JointAction n where
  bid := act.bid
  bid_nonneg := act.bid_nonneg
  routeCount := act.routeCount+1
  routeCount_le := hk

theorem focalCount_le_addRoute (Γ : FiniteGame (N+1) n c Seed) (i : Fin (N+1))
    (act : JointAction n) (hk : act.routeCount < n) (ω : Sample (N+1) n Seed) :
    (focalCount Γ i act ω).val ≤ (focalCount Γ i (ppiAddRoute act hk) ω).val := by
  classical
  change (accepted (deviated i act ω) Γ.policy ω.1.2 i).card ≤
    (accepted (deviated i (ppiAddRoute act hk) ω) Γ.policy ω.1.2 i).card
  apply Finset.card_le_card
  intro j hj
  have haj : i ∈ allocation (deviated i act ω) Γ.policy ω.1.2 j :=
    (Finset.mem_filter.mp hj).2
  obtain ⟨hr,ha⟩ := (mem_allocation_deviated_iff Γ i act ω j).mp haj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(mem_allocation_deviated_iff Γ i (ppiAddRoute act hk) ω j).mpr ?_⟩
  exact ⟨firstK_mono ω.2 (Nat.le_succ _) hr,ha⟩

theorem ppi_addRoute_load (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (i : Fin (N+1)) (act : JointAction n) (hk : act.routeCount < n) :
    ((problem Γ i).outcome (ppiAddRoute act hk)).load-
      ((problem Γ i).outcome act).load = meanAcceptProb Γ i act.bid := by
  rw [load_eq_mean Γ hn i,load_eq_mean Γ hn i]
  simp only [ppiAddRoute,Nat.cast_add,Nat.cast_one]
  ring

theorem ppi_addRoute_gain_ge (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (i : Fin (N+1)) (v : ℝ) (hv : 0 ≤ v)
    (act : JointAction n) (hk : act.routeCount < n) (ε : ℝ) (hε : 0 ≤ ε)
    (hq : 0 ≤ meanAcceptProb Γ i act.bid)
    (hpair : ∀ j l : Fin n, j ≠ l → ppiPairProb Γ i act.bid j l ≤
      ε*meanAcceptProb Γ i act.bid) :
    (v-act.bid)*meanAcceptProb Γ i act.bid-
        v*(n:ℝ)^2*ε*meanAcceptProb Γ i act.bid ≤
      (problem Γ i).payoff v (ppiAddRoute act hk)-(problem Γ i).payoff v act := by
  have hdup := ppi_duplicates_le_square_pair_bound Γ i (ppiAddRoute act hk)
    (meanAcceptProb Γ i act.bid) ε hq hε hpair
  have hload := ppi_addRoute_load Γ hn i act hk
  have hload_mul := congrArg (fun x : ℝ => (v-act.bid)*x) hload
  have hold := ((problem Γ i).outcome act).duplicates_nonneg
  have hnew := mul_le_mul_of_nonneg_left hdup hv
  have hold' := mul_nonneg hv hold
  rw [ppi_payoff_zero_fee Γ hA hg i v,ppi_payoff_zero_fee Γ hA hg i v]
  change _ ≤ v*((problem Γ i).outcome (ppiAddRoute act hk)).success-
    act.bid*((problem Γ i).outcome (ppiAddRoute act hk)).load-
    (v*((problem Γ i).outcome act).success-act.bid*((problem Γ i).outcome act).load)
  unfold CountLaw.duplicates at hnew hold'
  nlinarith [hload_mul]

theorem ppi_routeCount_eq_of_small_pair_and_rent
    (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (i : Fin (N+1)) (v : ℝ) (hv : 0 < v) (act : JointAction n)
    (hact : (problem Γ i).BestResponse v act)
    (R ε : ℝ) (hε : 0 ≤ ε) (hq : 0 < meanAcceptProb Γ i act.bid)
    (hrent : R*v/((N:ℝ)+1) ≤ v-act.bid)
    (hsmall : (n:ℝ)^2*ε < R/((N:ℝ)+1))
    (hpair : ∀ j l : Fin n, j ≠ l → ppiPairProb Γ i act.bid j l ≤
      ε*meanAcceptProb Γ i act.bid) : act.routeCount = n := by
  by_contra hh
  have hk : act.routeCount < n := lt_of_le_of_ne act.routeCount_le hh
  have hgain := ppi_addRoute_gain_ge Γ hn hA hg i v hv.le act hk ε hε hq.le hpair
  have hgainpos : 0 < (v-act.bid)*meanAcceptProb Γ i act.bid-
      v*(n:ℝ)^2*ε*meanAcceptProb Γ i act.bid := by
    have h1 := mul_lt_mul_of_pos_right hsmall hv
    have h2 := mul_lt_mul_of_pos_right h1 hq
    have h3 := mul_le_mul_of_nonneg_right hrent hq.le
    have he : R/((N:ℝ)+1)*v = R*v/((N:ℝ)+1) := by ring
    rw [he] at h2
    nlinarith
  have hbr := hact (ppiAddRoute act hk)
  linarith

end FCAppendix.Bayes
