import FCAppendix.Affine.Tail04.NativeFlagTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open MeasureTheory ProbabilityTheory Set Filter
open NativeFlag
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

def rowBulk (E : Set X) (row : Fin N → X) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => row i ∈ E)

omit [MeasurableSpace X] in
lemma rowBulk_card (E : Set X) (row : Fin N → X) :
    (rowBulk E row).card = Probability.sampleCount E row := by
  classical
  rfl

theorem weighted_bound_antitone_card {epsilon small large : ℝ}
    (heps : 0 < epsilon) (hsmall : 0 < small) (hlarge : small ≤ large) (r : ℕ) :
    2/(epsilon*large)+(r:ℝ)*Real.sqrt (2/(epsilon*large+1)) ≤
      2/(epsilon*small)+(r:ℝ)*Real.sqrt (2/(epsilon*small+1)) := by
  have hprod := mul_le_mul_of_nonneg_left hlarge heps.le
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos heps hsmall) hprod
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

def rowForcedLaw (T : (Fin N → X) → FiniteLaw (Fin N))
    (p : (Fin N → X) → Fin N → ℝ)
    (hp0 : ∀ row i, 0 ≤ p row i) (hp1 : ∀ row i, p row i ≤ 1)
    (row : Fin N → X) : FiniteLaw (Fin N × (Fin N → Bool)) :=
  ((T row).prod (BidDependentFlags.flags (p row) (hp0 row) (hp1 row))).map
    (fun z => (z.1,forceExclusive z.1 z.2))

lemma measurable_rowForcedLaw_mass
    (T : (Fin N → X) → FiniteLaw (Fin N))
    (hT : ∀ i, Measurable (fun row => (T row).mass i))
    (p : (Fin N → X) → Fin N → ℝ)
    (hp0 : ∀ row i, 0 ≤ p row i) (hp1 : ∀ row i, p row i ≤ 1)
    (hp : ∀ i, Measurable (fun row => p row i)) (z : Fin N × (Fin N → Bool)) :
    Measurable (fun row => (rowForcedLaw T p hp0 hp1 row).mass z) := by
  classical
  simp only [rowForcedLaw, FiniteLaw.map, FiniteLaw.prod]
  apply Finset.measurable_sum
  intro x _
  by_cases hx : (x.1,forceExclusive x.1 x.2)=z
  · simp only [if_pos hx]
    exact (hT x.1).mul (measurable_independentFlagLaw_mass p hp0 hp1 hp x.2)
  · simp only [if_neg hx]
    exact measurable_const

theorem iid_forced_weighted_interval (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (hN : 0 < N)
    {rho epsilon a C : ℝ} (hrho : 0 < rho) (hmass : rho ≤ μ.real E)
    (heps : 0 < epsilon) (heps' : epsilon < 1/2) (ha : 0 < a)
    (T : (Fin N → X) → FiniteLaw (Fin N))
    (hT : ∀ i, Measurable (fun row => (T row).mass i))
    (p w : (Fin N → X) → Fin N → ℝ)
    (hp0 : ∀ row i, 0 ≤ p row i) (hp1 : ∀ row i, p row i ≤ 1)
    (hp : ∀ i, Measurable (fun row => p row i))
    (hw : ∀ i, Measurable (fun row => w row i))
    (hbulk : ∀ row i, row i ∈ E →
      epsilon ≤ p row i ∧ p row i ≤ 1-epsilon ∧ a ≤ |w row i|)
    (hweights : ∀ row i, |w row i| ≤ C)
    (l : (Fin N → X) → ℝ) (hl : Measurable l)
    (r rWide : ℕ) (hwidth : (r:ℝ)*a+2*C ≤ (rWide:ℝ)*a) :
    (∫ row, (rowForcedLaw T p hp0 hp1 row).prob
      (fun z => weightedSum (w row) z.2 ∈ Ico (l row) (l row+(r:ℝ)*a))
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (-(N:ℝ)*rho^2/2) +
        (2/(epsilon*(rho*(N:ℝ)/2))+
          (rWide:ℝ)*Real.sqrt (2/(epsilon*(rho*(N:ℝ)/2)+1))) := by
  classical
  let bad : Set (Fin N → X) :=
    {row | (Probability.sampleCount E row : ℝ) < rho*(N:ℝ)/2}
  let P : (Fin N → X) → (Fin N × (Fin N → Bool)) → Prop :=
    fun row z => weightedSum (w row) z.2 ∈ Ico (l row) (l row+(r:ℝ)*a)
  let K := 2/(epsilon*(rho*(N:ℝ)/2))+
    (rWide:ℝ)*Real.sqrt (2/(epsilon*(rho*(N:ℝ)/2)+1))
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hsmall : 0 < rho*(N:ℝ)/2 := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbad : MeasurableSet bad := measurableSet_lt
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (Probability.measurable_sampleCount E hE N)) measurable_const
  have hP (z : Fin N × (Fin N → Bool)) : MeasurableSet {row | P row z} := by
    have hs : Measurable (fun row => weightedSum (w row) z.2) :=
      Finset.measurable_sum _ (fun i _ => (hw i).mul_const _)
    exact (measurableSet_le hl hs).inter
      (measurableSet_lt hs (hl.add_const _))
  have hgood (row : Fin N → X) (hrow : row ∉ bad) :
      (rowForcedLaw T p hp0 hp1 row).prob (P row) ≤ K := by
    have hcard : rho*(N:ℝ)/2 ≤ ((rowBulk E row).card:ℝ) := by
      simpa only [rowBulk_card] using (le_of_not_gt hrow)
    have hJ : (rowBulk E row).Nonempty := by
      apply Finset.card_pos.mp
      have hpos : 0 < ((rowBulk E row).card:ℝ) := hsmall.trans_le hcard
      exact_mod_cast hpos
    have hb i (hi : i ∈ rowBulk E row) := hbulk row i (by
      simpa only [rowBulk,Finset.mem_filter,Finset.mem_univ,true_and] using hi)
    have hfinite := forced_interval_from_bulk (T row) (p row) (w row)
      (hp0 row) (hp1 row) (rowBulk E row) hJ heps heps'
      (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2.1) ha
      (fun i hi => (hb i hi).2.2) (hweights row) (l row) r rWide hwidth
    have heq : (rowForcedLaw T p hp0 hp1 row).prob (P row) =
        ((T row).prod (BidDependentFlags.flags (p row) (hp0 row) (hp1 row))).prob
          (fun z => weightedSum (w row) (forceExclusive z.1 z.2) ∈
            Ico (l row) (l row+(r:ℝ)*a)) := by
      simp only [rowForcedLaw,FiniteLaw.prob_eq_expect,FiniteLaw.expect_map,P]
    rw [heq]
    exact hfinite.trans (weighted_bound_antitone_card heps hsmall hcard rWide)
  have hi := integral_probability_le_bad_add
    (Measure.pi (fun _ : Fin N => μ)) (rowForcedLaw T p hp0 hp1)
    (measurable_rowForcedLaw_mass T hT p hp0 hp1 hp) P hP bad hbad hK hgood
  exact hi.trans (add_le_add (by
    simpa only [bad] using iid_bulk_count_lower_tail μ E hE N hN hrho hmass) le_rfl)

end FCAppendix.Affine.Tail04.WeightedFlagBound
