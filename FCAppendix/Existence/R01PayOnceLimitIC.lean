import FCAppendix.Existence.R01PayOnceImprovementError

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

theorem improvementMass_limit_eq_zero {W : ℝ} (hW : 0<W)
    (N n c : ℕ) (hn : 2≤n)
    (ν : ℕ→ProbabilityMeasure (Value W × FloorAction 0 W))
    (ν₀ : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hν : Tendsto ν atTop (𝓝 ν₀))
    (hzero : (ν₀ : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0)
    (b : FloorAction 0 W) (cap : ℝ) (hcap : 0<cap) (hcapW : cap≤W)
    (hb : present b=true→cap≤bid b)
    (hM : ∀ᶠj in atTop,improvementMass N n c (ν j) b=0) :
    improvementMass N n c ν₀ b=0 := by
  let K : ℝ := (4*W)*(N+1)
  have hK : 0≤K := by dsimp [K]; positivity
  have hnonneg : 0≤ improvementMass N n c ν₀ b := integral_nonneg (fun _=>le_max_left _ _)
  by_contra hne
  have hpos : 0 < improvementMass N n c ν₀ b := lt_of_le_of_ne hnonneg (Ne.symm hne)
  let r : ℝ := improvementMass N n c ν₀ b/(4*(K+1))
  have hr : 0<r := by dsimp [r]; positivity
  have hKr : 2*K*r< improvementMass N n c ν₀ b := by
    have heq : r*(4*(K+1))=improvementMass N n c ν₀ b := by dsimp [r]; field_simp
    nlinarith
  let δ : ℕ→ℝ := fun k=>cap/(k+1)
  have hδ : ∀k,0<δ k := by intro k; dsimp [δ]; positivity
  have hδcap : ∀k,δ k≤cap := by
    intro k
    apply (div_le_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
    nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  have hδW : ∀k,δ k≤W := fun k=>(hδcap k).trans hcapW
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) using 1
    · funext k; dsimp [δ]; ring
    · simp
  have hmass := smallActive_mass_tendsto_zero ν₀ hzero δ hδ0
  obtain ⟨k,hk⟩ := (hmass.eventually (Iio_mem_nhds hr)).exists
  have hbsafe : present b=true→δ k≤bid b := fun h=>(hδcap k).trans (hb h)
  let C := fun π : ProbabilityMeasure (Value W × FloorAction 0 W)=>
    clippedImprovementMass N n c (δ k) (hδW k) π b
  have hC : Tendsto (fun j=>C (ν j)) atTop (𝓝 (C ν₀)) :=
    (((continuous_clippedImprovementMass N n c hn (δ k) (hδ k) (hδW k)).comp
      (continuous_id.prodMk continuous_const)).continuousAt.tendsto.comp hν)
  have hMlt := eventually_closed_mass_lt ν ν₀ hν (smallActive (δ k))
    (isClosed_smallActive (δ k)) r hk
  have hCbound : ∀ᶠj in atTop,C (ν j)≤K*r := by
    filter_upwards [hM,hMlt] with j hjM hjmass
    have he := improvementMass_clipping_error hW.le N n c hn (δ k) (hδ k)
      (hδW k) (ν j) b hbsafe
    have hupper := (abs_le.mp he).2
    have hm := mul_le_mul_of_nonneg_left hjmass.le hK
    change C (ν j)-improvementMass N n c (ν j) b≤
      K*(ν j : Measure (Value W × FloorAction 0 W)).real (smallActive (δ k)) at hupper
    rw [hjM,sub_zero] at hupper
    exact hupper.trans hm
  have hlim : C ν₀≤K*r := le_of_tendsto hC hCbound
  have he := improvementMass_clipping_error hW.le N n c hn (δ k) (hδ k)
    (hδW k) ν₀ b hbsafe
  have hlower := (abs_le.mp he).1
  have hm := mul_le_mul_of_nonneg_left hk.le hK
  change -(K*(ν₀ : Measure (Value W × FloorAction 0 W)).real (smallActive (δ k)))≤
    C ν₀-improvementMass N n c ν₀ b at hlower
  linarith

theorem actual_floor_limit_positive_improvement_zero (W : ℝ) (hW : 0<W)
    (N n c : ℕ) (hn : 2≤n) (μ : Measure (Value W)) [IsProbabilityMeasure μ]
    (ε : ℕ→ℝ) (hε : ∀j,0<ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (π : (j:ℕ)→FloorLaw (ε j) W μ)
    (hIC : ∀j,AllActionOptimal (π j) (fun z=>floorPayoff N n c (π j,z)))
    (ν₀ : FloorLaw 0 W μ)
    (hν : Tendsto (fun j=>(embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1))
    (hzero : (ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0) (b : PositiveBid W) :
    improvementMass N n c ν₀.1 (positiveAction b)=0 := by
  apply improvementMass_limit_eq_zero hW N n c hn _ ν₀.1 hν hzero (positiveAction b)
    b.1 b.2.1 b.2.2 (fun _=>le_rfl)
  have he := hε0.eventually (Iio_mem_nhds b.2.1)
  filter_upwards [he] with j hj
  let bj : Icc (ε j) W := ⟨b.1,hj.le,b.2.2⟩
  have hh := improvementMass_embeddedFloor_eq_zero N n c hn (hε j) (π j) (hIC j) bj
  convert hh using 1
  congr 1

theorem actual_floor_limit_inactive_improvement_zero (W : ℝ) (hW : 0<W)
    (N n c : ℕ) (hn : 2≤n) (μ : Measure (Value W)) [IsProbabilityMeasure μ]
    (ε : ℕ→ℝ) (hε : ∀j,0<ε j)
    (π : (j:ℕ)→FloorLaw (ε j) W μ)
    (hIC : ∀j,AllActionOptimal (π j) (fun z=>floorPayoff N n c (π j,z)))
    (ν₀ : FloorLaw 0 W μ)
    (hν : Tendsto (fun j=>(embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1))
    (hzero : (ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0) :
    improvementMass N n c ν₀.1 (.inl ())=0 := by
  apply improvementMass_limit_eq_zero hW N n c hn _ ν₀.1 hν hzero (.inl ()) W hW le_rfl
    (fun h=>False.elim (Bool.false_ne_true h))
  exact Filter.Eventually.of_forall (fun j=>
    improvementMass_embeddedFloor_inactive_eq_zero N n c hn (hε j) (π j) (hIC j))

theorem common_allAction_IC_of_improvementMass_zero {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hW : 0≤W) (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hM : ∀b : PositiveBid W,improvementMass N n c π (positiveAction b)=0)
    (hInactive : improvementMass N n c π (.inl ())=0) :
    ∀ᵐz ∂(π : Measure (Value W × FloorAction 0 W)),∀a : FloorAction 0 W,
      positivePayoff N n c π (z.1,a)≤positivePayoff N n c π z := by
  filter_upwards [common_positive_IC_of_improvementMass_zero N n c hn hW π hM,
    fixed_action_IC_of_improvementMass_zero N n c hn hW π (.inl ()) hInactive] with z hz hi
  have h0 : 0≤positivePayoff N n c π z := by simpa only [positivePayoff_inactive N n c hn π] using hi
  intro a
  cases a with
  | inl u => cases u; exact hi
  | inr b =>
    by_cases hb : b.1=0
    · change (z.1.1-b.1)*positiveQ N n c π (.inr b)≤_
      rw [positiveQ_zero_bid N n c hn π (.inr b) hb,mul_zero]
      exact h0
    · let bpos : PositiveBid W := ⟨b.1,lt_of_le_of_ne b.2.1 (Ne.symm hb),b.2.2⟩
      exact hz bpos

end FCAppendix.Existence.PayOnceBounded
