import FCAppendix.Finite.AmplePairRanks
import FCAppendix.Ample.PositiveBaseCounts
import FCAppendix.Finite.PPIRouteExclusion

noncomputable section

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def RejectsZeroBids (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ (j : Fin n) (ℓ : LocalList m) (z : Seed) (i : Fin m),
    ℓ i = some 0 → i ∉ (Γ.policy j ℓ z).val

lemma meanAcceptProb_zero_of_rejectsZero (Γ : FiniteGame m n c Seed)
    (hzero : RejectsZeroBids Γ) (i : Fin m) : meanAcceptProb Γ i 0 = 0 := by
  have hz (j : Fin n) : {ω : Background m n Seed | Accepts Γ i 0 j ω} = ∅ := by
    ext ω
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact hzero j (presentList ω i 0 j) (ω.2 j) i (presentList_self ω i 0 j)
  simp [meanAcceptProb, acceptProb, hz]

lemma success_zero_of_bid_zero (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (hzero : RejectsZeroBids Γ) (i : Fin m) (act : JointAction n) (hb : act.bid = 0) :
    ((problem Γ i).outcome act).success = 0 := by
  have hh := success_le_n_meanAcceptProb Γ hn i act
  rw [hb, meanAcceptProb_zero_of_rejectsZero Γ hzero, mul_zero] at hh
  exact le_antisymm hh (CountLaw.success_nonneg _)

namespace ReceiptSequenceAssumptions

variable {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g ρ : ℝ}

omit [IsProbabilityMeasure F] in
private theorem ample_opponent_population_grows
    (h : ReceiptSequenceAssumptions (fun k => N k + 1) C Γ B F g 1 ρ) :
    Tendsto N atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [h.population_grows.eventually_ge_atTop (b + 1)] with k hk
  omega

omit [IsProbabilityMeasure F] in
private theorem ample_opponent_capacity_ratio
    (h : ReceiptSequenceAssumptions (fun k => N k + 1) C Γ B F g 1 ρ) :
    Tendsto (fun k => (C k : ℝ) / N k) atTop (𝓝 ρ) := by
  have hinv : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h.ample_opponent_population_grows)
  have hfac : Tendsto (fun k => 1 + (N k : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using hinv.const_add 1
  have ht := h.capacity_ratio.mul hfac
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [h.ample_opponent_population_grows.eventually_ge_atTop 1] with k hk
  have hN : (N k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : (N k : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

theorem ample_positive_base_one_route_of_capacity
    (h : ReceiptSequenceAssumptions (fun k => N k + 1) C Γ B F g 1 ρ)
    (hn : 2 ≤ n) (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) (hzero : ∀ k, RejectsZeroBids (Γ k))
    (hc : ∀ k, 0 < C k) (hC : ∀ k, C k ≤ N k + 1)
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (i : ∀ k, Fin (N k + 1)) (v : ℝ) (hv : g < v) :
    ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr h.proposers_pos
  have hε : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have ham : F.real (Ioi g) < (n : ℝ) * ρ * (1 : ℝ) ^ 2 := by simpa using hample
  obtain ⟨δ, hδ, hdup⟩ := uniform_nonrare_ample_ppi_duplicates_pos hn N C Γ i hA
    h.visible_atomless h.feasible_continuations h.ample_opponent_population_grows hC
    h.ratio_pos h.ratio_lt_one (F.real (Ioi g)) measureReal_le_one hample
    (fun k b hb j l => by
      have hh := aboveAt_union_le_active (Γ k) (by omega) (hc k) (h.equilibria k) j l b hb.le
      simpa only [h.common_values k, h.common_fee k] using hh)
    h.ample_opponent_capacity_ratio (1 / (2 * (n : ℝ))) hε
  filter_upwards [hdup, h.ample_bestResponses hg ham i v hv (1 / 2) (by norm_num),
    h.ample_positive_base_duplicates_uniform hg ham d hd hG v hv δ hδ] with k hk hs hD
  intro act hbr
  have hS : (1 / 2 : ℝ) < ((problem (Γ k) (i k)).outcome act).success := by
    have hh := (hs act hbr).1
    linarith
  have hbid : 0 < act.bid := by
    by_contra hb
    have hz : act.bid = 0 := le_antisymm (le_of_not_gt hb) act.bid_nonneg
    rw [success_zero_of_bid_zero (Γ k) h.proposers_pos (hzero k) (i k) act hz] at hS
    norm_num at hS
  have hkpos : 0 < act.routeCount := by
    by_contra hnot
    have he : act.routeCount = 0 := by omega
    have hh := load_le_routeCount_mul_success (Γ k) (i k) act
    rw [he, Nat.cast_zero, zero_mul] at hh
    have hl := ((problem (Γ k) (i k)).outcome act).success_le_load
    linarith
  have hq := success_le_n_meanAcceptProb (Γ k) h.proposers_pos (i k) act
  rw [ppi_meanAcceptProb_eq_rank (Γ k) (hA k) (h.visible_atomless k)
    (h.feasible_continuations k) (i k) (⟨0, by omega⟩ : Fin n) act.bid hbid] at hq
  have hrank : 1 / (2 * (n : ℝ)) ≤ binomBelow (N k)
      (alphaGt (Γ k) (⟨0, by omega⟩ : Fin n) act.bid) (C k) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith
  have hnot : ¬ 2 ≤ act.routeCount := by
    intro ha
    exact not_le_of_gt (hD (i k) act hbr) (hk act hbid ha hrank)
  omega

theorem ample_positive_base_one_route
    {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {B : ∀ k, PosteriorSystem (Γ k)} {a : ℝ}
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (hn : 2 ≤ n) (hg : F {g} = 0) (hample : F.real (Ioi g) < (n : ℝ) * ρ)
    (hA : ∀ k, (Γ k).A = Schedule.ppi n) (hzero : ∀ k, RejectsZeroBids (Γ k))
    (d : ℝ) (hd : 0 < d)
    (hG : ∀ k r, 2 ≤ r → r ≤ n → d ≤ g * ((Γ k).G.charge r - 1))
    (i : ∀ k, Fin (M k)) (v : ℝ) (hv : g < v) :
    ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1 := by
  generalize hN : (fun k => M k - 1) = N
  have he : M = (fun k => N k + 1) := by
    funext k
    have hk := congrFun hN k
    have hpos := (i k).isLt
    omega
  subst M
  let h1 : ReceiptSequenceAssumptions (fun k => N k + 1) C Γ B F g 1 ρ :=
    { h with
      factor_pos := by norm_num
      receipt_lower := by intro k r _ _; simp [hA k, Schedule.ppi] }
  have hcap : ∀ᶠ k in atTop, C k ≤ N k + 1 := by
    filter_upwards [h1.capacity_ratio.eventually (eventually_lt_nhds h1.ratio_lt_one)]
      with k hk
    have hh : (C k : ℝ) < (N k + 1 : ℕ) :=
      (div_lt_one (by positivity : (0 : ℝ) < (N k + 1 : ℕ))).mp hk
    exact le_of_lt (by exact_mod_cast hh)
  obtain ⟨L, hL⟩ := eventually_atTop.mp (h1.eventually_capacity_pos.and hcap)
  have ht := (h1.along (fun k => k + L) (tendsto_add_atTop_nat L)).ample_positive_base_one_route_of_capacity
    hn hg hample (fun k => hA (k + L)) (fun k => hzero (k + L))
    (fun k => (hL (k + L) (by omega)).1) (fun k => (hL (k + L) (by omega)).2)
    d hd (fun k => hG (k + L)) (fun k => i (k + L)) v hv
  have hshift : ∀ᶠ k in Filter.map (fun k : ℕ => k + L) atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1 := ht
  simpa only [map_add_atTop_eq_nat] using hshift

end ReceiptSequenceAssumptions
end FCAppendix.Bayes
