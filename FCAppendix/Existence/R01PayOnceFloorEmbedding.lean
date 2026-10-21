import FCAppendix.Existence.R01PayOnceClassIC
import FCAppendix.Existence.R01PayOnceOpenLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

def embedFloor {ε W : ℝ} (hε : 0 ≤ ε) : FloorAction ε W → FloorAction 0 W
  | .inl u => .inl u
  | .inr b => .inr ⟨b.1,hε.trans b.2.1,b.2.2⟩

theorem continuous_embedFloor {ε W : ℝ} (hε : 0 ≤ ε) : Continuous (embedFloor (W := W) hε) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_inl
  · exact continuous_inr.comp (continuous_subtype_val.subtype_mk _)

@[simp] theorem present_embedFloor {ε W : ℝ} (hε : 0 ≤ ε) (b : FloorAction ε W) :
    present (embedFloor hε b)=present b := by cases b <;> rfl

@[simp] theorem bid_embedFloor {ε W : ℝ} (hε : 0 ≤ ε) (b : FloorAction ε W) :
    bid (embedFloor hε b)=bid b := by cases b <;> rfl

def embedFloorPair {ε W : ℝ} (hε : 0 ≤ ε)
    (z : Value W × FloorAction ε W) : Value W × FloorAction 0 W :=
  (z.1,embedFloor hε z.2)

theorem continuous_embedFloorPair {ε W : ℝ} (hε : 0 ≤ ε) :
    Continuous (embedFloorPair (W := W) hε) :=
  continuous_fst.prodMk ((continuous_embedFloor hε).comp continuous_snd)

def embeddedFloorLaw {ε W : ℝ} (hε : 0 ≤ ε) {μ : Measure (Value W)}
    (π : FloorLaw ε W μ) : FloorLaw 0 W μ := by
  let e := embedFloorPair (W := W) hε
  let ν := π.1.map (continuous_embedFloorPair hε).measurable.aemeasurable
  refine ⟨ν,?_⟩
  change (Measure.map e (π.1 : Measure _)).map Prod.fst=μ
  rw [Measure.map_map measurable_fst (continuous_embedFloorPair hε).measurable]
  exact π.2

theorem embeddedFloorLaw_nearActive {ε W : ℝ} (hε : 0 ≤ ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (a t : ℝ) :
    ((embeddedFloorLaw hε π).1 : Measure (Value W × FloorAction 0 W)).real (nearActive a t) =
      (π.1 : Measure (Value W × FloorAction ε W)).real {z | smallClass a t z} := by
  have hC : MeasurableSet (nearActive (W := W) a t) := measurableSet_smallClass a t
  change (Measure.map (embedFloorPair hε) (π.1 : Measure (Value W × FloorAction ε W))).real (nearActive a t)=_
  rw [Measure.real, Measure.map_apply (continuous_embedFloorPair hε).measurable hC]
  congr 2
  ext z
  simp [nearActive, smallClass, embedFloorPair]

theorem embeddedFloorLaw_small_bid_power {ε W : ℝ} (N n c : ℕ)
    (hN : 0 < N) (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < N+1) (hε : 0 < ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z => floorPayoff N n c (π,z)))
    (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (hεB : ε ≤ 2*n*t) (hBW : 2*n*t ≤ W) :
    (((embeddedFloorLaw hε.le π).1 : Measure (Value W × FloorAction 0 W)).real
      (nearActive a t))^N ≤ (2*n*t)/(a*(1-PayOnce.success n ((c:ℝ)/(N+1)))) := by
  rw [embeddedFloorLaw_nearActive]
  exact floor_equilibrium_small_bid_power N n c hN hn hc1 hcm hε π hIC a t ha ht
    ⟨2*n*t,hεB,hBW⟩ rfl

theorem actual_floor_limit_no_positive_active_zero (W : ℝ) (hW : 0 < W)
    (N n c : ℕ) (hN : 0 < N) (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c < N+1)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ]
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (π : (j : ℕ) → FloorLaw (ε j) W μ)
    (hIC : ∀ j, AllActionOptimal (π j) (fun z => floorPayoff N n c (π j,z)))
    (ν₀ : FloorLaw 0 W μ)
    (hν : Tendsto (fun j => (embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1)) :
    (ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z | 0 < z.1.1 ∧ present z.2=true ∧ bid z.2=0}=0 := by
  let gap := 1-PayOnce.success n ((c:ℝ)/(N+1))
  have hgap : 0 < gap := by
    simpa only [gap,Nat.cast_add,Nat.cast_one] using
      capacity_success_gap_pos n (N+1) c (Nat.succ_pos _) hcm
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let δ : ℝ := W/(2*n)
  have hδ : 0<δ := div_pos hW (by positivity)
  apply no_positive_active_zero_of_power_bound
    (fun j => (embeddedFloorLaw (hε j).le (π j)).1) ν₀.1 hν N hN δ hδ
    (fun a => (2*n)/(a*gap))
    (fun a ha => by positivity)
  intro a ha t ht htδ
  have hεB : ∀ᶠ j in atTop, ε j ≤ 2*n*t := by
    have hpos : (0:ℝ)<2*n*t := by positivity
    exact (hε0.eventually (Iio_mem_nhds hpos)).mono (fun _ h => h.le)
  filter_upwards [hεB] with j hj
  have hBW : 2*n*t ≤ W := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<2*n)).mp htδ
    nlinarith
  have hh := embeddedFloorLaw_small_bid_power N n c hN hn hc1 hcm (hε j)
    (π j) (hIC j) a t ha ht hj hBW
  convert hh using 1
  dsimp [gap]
  ring

theorem exists_floor_limit_without_positive_active_zero (W : ℝ) (hW : 0<W)
    (N n c : ℕ) (hN : 0<N) (hn : 2≤n) (hc1 : 1≤c) (hcm : c<N+1)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] :
    ∃ (ε : ℕ→ℝ) (hε : ∀j,0<ε j) (π : (j:ℕ)→FloorLaw (ε j) W μ)
      (ν₀ : FloorLaw 0 W μ),
      (∀j,ε j≤W) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀j,AllActionOptimal (π j) (fun z=>floorPayoff N n c (π j,z))) ∧
      Tendsto (fun j=>(embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1) ∧
      (ν₀.1 : Measure (Value W × FloorAction 0 W))
        {z|0<z.1.1 ∧ present z.2=true ∧ bid z.2=0}=0 := by
  let ε : ℕ→ℝ := fun j=>W/(j+1)
  have hε : ∀j,0<ε j := by intro j; dsimp [ε]; positivity
  have hεW : ∀j,ε j≤W := by
    intro j
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<j+1)).mpr
    nlinarith [show (0:ℝ)≤j from Nat.cast_nonneg j]
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) using 1
    · funext j; dsimp [ε]; ring
    · simp
  choose π σ hσ hcomp hIC htype using
    (fun j=>epsilon_floor_exists W (ε j) (hε j) (hεW j) N n c hn μ)
  obtain ⟨ν₀,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq
    (fun j=>embeddedFloorLaw (hε j).le (π j))
  refine ⟨ε ∘ φ,(fun j=>hε (φ j)),(fun j=>π (φ j)),ν₀,
    (fun j=>hεW (φ j)),hε0.comp hφ.tendsto_atTop,(fun j=>hIC (φ j)),?_,?_⟩
  · exact continuous_subtype_val.continuousAt.tendsto.comp hlim
  · exact actual_floor_limit_no_positive_active_zero W hW N n c hN hn hc1 hcm μ
      (ε ∘ φ) (fun j=>hε (φ j)) (hε0.comp hφ.tendsto_atTop)
      (fun j=>π (φ j)) (fun j=>hIC (φ j)) ν₀
      (continuous_subtype_val.continuousAt.tendsto.comp hlim)

end FCAppendix.Existence.PayOnceBounded
