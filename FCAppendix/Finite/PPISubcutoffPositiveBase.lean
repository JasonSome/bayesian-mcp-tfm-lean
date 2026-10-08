import FCAppendix.Finite.PPISubcutoffBroadcast
import FCAppendix.Finite.PPISubcutoffNetMass
import FCAppendix.Finite.PPISubcutoffNetRank
import FCAppendix.Finite.PPISubcutoffZeroPair

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure PPISubcutoffPositiveBaseRow {N c : ℕ}
    (Γ : FiniteGame (N+1) n c Seed) (F : Measure ℝ) (g ρ : ℝ) : Prop where
  common_values : Γ.F = F
  common_fee : Γ.g = g
  ppi : Γ.A = Schedule.ppi n
  base_ppi : Γ.G = Schedule.ppi n
  capacity_exact : (c:ℝ) = ρ*((N:ℝ)+1)
  equilibrium : IsAEEquilibrium Γ
  feasible_continuations : ∀ j, ProposerRationalAtFeasibleLists Γ j
  visible_atomless : VisibleAtomless Γ
  policy_symmetry : PolicyLawEquivariant Γ

namespace PPISubcutoffPositiveBaseRow
variable {N c : ℕ} {Γ : FiniteGame (N+1) n c Seed} {F : Measure ℝ} {g ρ : ℝ}

lemma positive_visible (h : PPISubcutoffPositiveBaseRow Γ F g ρ) :
    PositiveVisibleAtomless Γ :=
  VisibleAtomless.positive Γ h.visible_atomless

lemma visible_zero (h : PPISubcutoffPositiveBaseRow Γ F g ρ) (j : Fin n) :
    visibleBidMeasure Γ j {0} = 0 :=
  visibleBidMeasure_singleton_of_full_atomlessness Γ h.visible_atomless j 0

lemma capacity_pos (h : PPISubcutoffPositiveBaseRow Γ F g ρ) (hρ : 0 < ρ) :
    0 < c := by
  have hh : (0 : ℝ) < c := by rw [h.capacity_exact]; positivity
  exact_mod_cast hh

lemma capacity_lt (h : PPISubcutoffPositiveBaseRow Γ F g ρ) (hρ : ρ < 1) :
    c < N+1 := by
  have hh := mul_lt_mul_of_pos_right hρ (show 0 < (N : ℝ)+1 by positivity)
  rw [← h.capacity_exact, one_mul] at hh
  exact_mod_cast hh

end PPISubcutoffPositiveBaseRow

theorem ppi_positive_base_rows_nearPPI
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n:ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffPositiveBaseRow (Γ k) F g ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop) :
    NearPPIAssumptions (fun k => N k+1) C Γ F g (fun _ => 1) ρ vstar := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hρ1 : ρ < 1 := by
    have hmass : F.real (Ioi g) ≤ 1 := measureReal_le_one
    nlinarith [mul_le_mul_of_nonneg_right hn1 hρ.le]
  apply CongestedAssumptions.nearPPI_of_ppi (hA := fun k => (hrows k).ppi)
  refine {
    proposers_two := hn
    capacity_lt_population := ?_
    common_values := fun k => (hrows k).common_values
    common_fee := fun k => (hrows k).common_fee
    ratio_pos := hρ
    ratio_lt_one := hρ1
    population_grows := hpop
    capacity_ratio := ?_
    equilibria := fun k => (hrows k).equilibrium
    feasible_continuations := fun k => (hrows k).feasible_continuations
    visible_atomless := fun k => VisibleAtomless.positive (Γ k) (hrows k).visible_atomless
    policy_symmetry := fun k => (hrows k).policy_symmetry
    scarcity := hscarce
    efficient_cutoff := hcut
    local_density := d.local_density }
  · intro k
    have hh := mul_lt_mul_of_pos_right hρ1 (show 0 < (N k:ℝ)+1 by positivity)
    rw [← (hrows k).capacity_exact,one_mul] at hh
    exact_mod_cast hh
  · have he : (fun k => (C k:ℝ)/(N k+1:ℕ)) = fun _ : ℕ => ρ := by
      funext k
      rw [Nat.cast_add,Nat.cast_one,(hrows k).capacity_exact]
      have hm : (N k : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hm]
    rw [he]
    exact tendsto_const_nhds

variable {N c : ℕ}

lemma ppi_payoff_per_inclusion_base (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hG : Γ.G = Schedule.ppi n)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction n) :
    (problem Γ i).payoff v act = v*((problem Γ i).outcome act).success -
      (act.bid+Γ.g)*((problem Γ i).outcome act).load := by
  change ((problem Γ i).outcome act).utility v act.bid Γ.g Γ.A Γ.G = _
  simp only [CountLaw.utility_eq, hA, hG, CountLaw.charge_ppi]
  ring

theorem ppi_zero_rank_le_n_actual_mean_of_bestResponse
    (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (i : Fin (N+1)) (j : Fin n)
    (v : ℝ) (hv : Γ.g < v) (act : JointAction n)
    (hact : (problem Γ i).BestResponse v act) :
    binomBelow N (alphaGt Γ j 0) c ≤ (n:ℝ)*meanAcceptProb Γ i act.bid := by
  have hs := ppi_success_ge_zero_rank Γ hA hj hatom i j (v-Γ.g)
    (sub_pos.mpr hv) act (by
      have hshift : Γ.g + (v-Γ.g) = v := by ring
      simpa only [hshift] using hact)
  exact hs.trans (success_le_n_meanAcceptProb Γ hn i act)

theorem ppi_positive_base_addRoute_gain
    (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hG : Γ.G = Schedule.ppi n)
    (i : Fin (N+1)) (v : ℝ) (hv : 0 ≤ v)
    (act : JointAction n) (hk : act.routeCount < n) (e : ℝ) (he : 0 ≤ e)
    (hq : 0 ≤ meanAcceptProb Γ i act.bid)
    (hpairs : ∀ j l : Fin n, j ≠ l →
      ppiPairProb Γ i act.bid j l ≤ e*meanAcceptProb Γ i act.bid) :
    (v-Γ.g-act.bid)*meanAcceptProb Γ i act.bid -
        v*(n:ℝ)^2*e*meanAcceptProb Γ i act.bid ≤
      (problem Γ i).payoff v (ppiAddRoute act hk)-(problem Γ i).payoff v act := by
  have hdup := ppi_duplicates_le_square_pair_bound Γ i (ppiAddRoute act hk)
    (meanAcceptProb Γ i act.bid) e hq he hpairs
  have hload := ppi_addRoute_load Γ hn i act hk
  have hloadmul := congrArg (fun x : ℝ => (v-Γ.g-act.bid)*x) hload
  have hold := mul_nonneg hv ((problem Γ i).outcome act).duplicates_nonneg
  have hnew := mul_le_mul_of_nonneg_left hdup hv
  rw [ppi_payoff_per_inclusion_base Γ hA hG i v,
    ppi_payoff_per_inclusion_base Γ hA hG i v]
  change _ ≤ v*((problem Γ i).outcome (ppiAddRoute act hk)).success -
    (act.bid+Γ.g)*((problem Γ i).outcome (ppiAddRoute act hk)).load -
    (v*((problem Γ i).outcome act).success -
      (act.bid+Γ.g)*((problem Γ i).outcome act).load)
  unfold CountLaw.duplicates at hold hnew
  nlinarith [hloadmul]

theorem ppi_positive_base_routeCount_eq_of_rent_pairs
    (Γ : FiniteGame (N+1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hG : Γ.G = Schedule.ppi n)
    (i : Fin (N+1)) (v ζ V R e : ℝ) (hζ : 0 < ζ) (hR : 0 < R)
    (hv : Γ.g+ζ ≤ v) (hvV : v ≤ V) (he : 0 ≤ e)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act)
    (hq : 0 < meanAcceptProb Γ i act.bid)
    (hrent : R*(v-Γ.g)/((N:ℝ)+1) ≤ v-Γ.g-act.bid)
    (hsmall : V*(n:ℝ)^2*e < R*ζ/((N:ℝ)+1))
    (hpairs : ∀ j l : Fin n, j ≠ l →
      ppiPairProb Γ i act.bid j l ≤ e*meanAcceptProb Γ i act.bid) :
    act.routeCount = n := by
  have hm : 0 < (N:ℝ)+1 := by positivity
  have hv0 : 0 ≤ v := by linarith [Γ.g_nonneg]
  have hfloor : R*ζ/((N:ℝ)+1) ≤ v-Γ.g-act.bid := by
    apply le_trans _ hrent
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : ζ ≤ v-Γ.g) hR.le) hm.le
  have hcost : v*(n:ℝ)^2*e ≤ V*(n:ℝ)^2*e := by
    nlinarith [mul_le_mul_of_nonneg_right hvV (mul_nonneg (sq_nonneg (n:ℝ)) he)]
  have hmargin : v*(n:ℝ)^2*e < v-Γ.g-act.bid := hcost.trans_lt (hsmall.trans_le hfloor)
  by_contra hne
  have hk : act.routeCount < n := lt_of_le_of_ne act.routeCount_le hne
  have hgain := ppi_positive_base_addRoute_gain Γ hn hA hG i v hv0 act hk e he hq.le hpairs
  have hgainpos := mul_lt_mul_of_pos_right hmargin hq
  have hbr := hact (ppiAddRoute act hk)
  nlinarith

private theorem ppi_positive_base_rank_size_eventually
    (N : ℕ → ℕ) (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (n : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ᶠ k in atTop, (n : ℝ)*Real.exp (-Δ^2*((N k : ℝ)+1)) < 1 := by
  have hm : Tendsto (fun k => (N k : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp hpop
  have he : Tendsto (fun k => Real.exp (-Δ^2*((N k : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (hm.const_mul_atTop (sq_pos_of_pos hΔ))
  have he' : Tendsto (fun k => (n : ℝ)*Real.exp (-Δ^2*((N k : ℝ)+1)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (n : ℝ)
  exact he'.eventually (eventually_lt_nhds zero_lt_one)

theorem ppi_positive_base_subcutoff_estimates
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n : ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n : ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffPositiveBaseRow (Γ k) F g ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (i : ∀ k, Fin (N k+1)) (w : ℝ) (hgw : g < w) (hw : w < vstar) :
    ∃ R γ : ℝ, 0 < R ∧ 0 < γ ∧ ∀ᶠ k in atTop,
      ∀ v : ℝ, g < v → v ≤ w → ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      0 < meanAcceptProb (Γ k) (i k) act.bid ∧
      R*(v-g)/((N k : ℝ)+1) ≤ v-g-act.bid ∧
      ∀ j l : Fin n, j ≠ l → ppiPairProb (Γ k) (i k) act.bid j l ≤
        ((n : ℝ)*Real.exp (-γ*((N k : ℝ)+1)))*meanAcceptProb (Γ k) (i k) act.bid := by
  letI : NullSingletonClass F := d.nullSingletonClass
  let h := ppi_positive_base_rows_nearPPI N C Γ F g ρ vstar V hn hρ hscarce
    d hcut hrows hpop
  let j0 : Fin n := ⟨0, by omega⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn2 : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  let astar := F.real (Ioi w)/(n : ℝ)
  let Δ := (astar-ρ)/2
  let a := ρ+Δ
  obtain ⟨hastar, hastar1⟩ :=
    ppi_value_rank_gap F vstar V d hn ρ w (hg.le.trans hgw.le) hw hcut
  have hΔ : 0 < Δ := by dsimp [Δ, astar]; linarith
  have hra : ρ < a := by dsimp only [a]; linarith
  have ha : a < 1 := by dsimp [a, Δ, astar]; linarith
  obtain ⟨η, t, γ, hη, hηhalf, ht, hγ, hγeq⟩ :=
    exists_ppi_subcutoff_pair_decay ρ a hρ hra ha
  let δ := ((n : ℝ)-1)*ρ/2
  have hnminus : 0 < (n : ℝ)-1 := by linarith
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let θ := ppiSubcutoffTheta δ d.upper V
  let R := θ/(2*(n : ℝ)^2*Real.exp 1)
  have hV : 0 < V := d.cutoff_mem.1.trans d.cutoff_mem.2
  have hupper : 0 < d.upper := d.upper_pos
  have hθ : 0 < θ := by
    dsimp [θ, ppiSubcutoffTheta]
    exact lt_min (by norm_num) (by positivity)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hmass := h.ppi_subcutoff_mass_bounds_net i (fun k => (hrows k).ppi)
    V d w η hgw.le hw hη
  have hsize := ppi_positive_base_rank_size_eventually N hpop n Δ hΔ
  refine ⟨R, γ, hR, hγ, ?_⟩
  filter_upwards [hmass, hsize] with k hmassk hsizek
  let dk := d.changeMeasure (Γ k).F (hrows k).common_values
  letI : NullSingletonClass (Γ k).F := dk.nullSingletonClass
  have hc := (hrows k).capacity_pos hρ
  have hcN := ((hrows k).capacity_lt h.ratio_lt_one).le
  have hslack (j : Fin n) : alphaGt (Γ k) j 0 ≤ 1-δ := by
    have hupperk := hmassk.1 j
    have hh := mul_le_mul_of_nonneg_left hηhalf.le hnminus.le
    dsimp only [δ]
    nlinarith
  have hslack1 (j : Fin n) : alphaGt (Γ k) j 0 < 1 := by
    linarith [hslack j, hδ]
  intro v hv hvw act hact
  have hvk : (Γ k).g < v := by simpa only [(hrows k).common_fee] using hv
  have hpositive := ppi_positive_net_bestResponse_of_visible_slack (Γ k)
    (hrows k).ppi (hrows k).feasible_continuations (hrows k).positive_visible
    hc (i k) j0 (hslack1 j0) v hvk act hact
  have hq : 0 < meanAcceptProb (Γ k) (i k) act.bid := by
    have hprod : 0 < (n : ℝ)*meanAcceptProb (Γ k) (i k) act.bid :=
      hpositive.1.trans_le (success_le_n_meanAcceptProb (Γ k) hn0 (i k) act)
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hnR.le (le_of_not_gt hnot)
    exact (not_lt_of_ge hnonpos) hprod
  have hbidw : act.bid ≤ w-g := by
    calc
      act.bid ≤ v-(Γ k).g := hpositive.2.2.le
      _ ≤ w-g := by rw [(hrows k).common_fee]; linarith
  have hrank0 := ppi_subcutoff_net_rank_separation (Γ k) hn (hrows k).ppi
    (hrows k).feasible_continuations (hrows k).positive_visible
    (hrows k).equilibrium.users (hrows k).visible_zero hc hcN ρ hρ
    (hrows k).capacity_exact vstar V dk w
    (by simpa only [(hrows k).common_fee] using hgw.le) hw
    (by simpa only [(hrows k).common_values] using hcut) (i k) j0 (hslack1 j0)
    (by simpa only [Δ, astar, (hrows k).common_values] using hsizek)
    v hvk hvw act hact
  have hrank (j : Fin n) : a ≤ alphaGt (Γ k) j act.bid := by
    rw [alphaGt_eq (Γ k) j j0 act.bid]
    simpa only [a, Δ, astar, (hrows k).common_values] using hrank0
  have hactslack (j : Fin n) : alphaGt (Γ k) j act.bid < 1 :=
    (alphaGt_antitone (Γ k) j act.bid_nonneg).trans_lt (hslack1 j)
  have hpair : ∀ j l : Fin n, j ≠ l → ppiPairProb (Γ k) (i k) act.bid j l ≤
      ((n : ℝ)*Real.exp (-γ*((N k : ℝ)+1)))*meanAcceptProb (Γ k) (i k) act.bid := by
    intro j l hjl
    by_cases hb : 0 < act.bid
    · have hsharp := ppi_pair_acceptance_le_exp_of_mass_and_rank (Γ k)
        (hrows k).ppi (hrows k).positive_visible (hrows k).feasible_continuations
        hc hcN ρ a η t γ hρ h.ratio_lt_one ha (by linarith) ht.le
        (hrows k).capacity_exact hγeq (i k) j l act.bid hb
        (hrank j) (hactslack j) (hmassk.2 j l hjl act.bid hbidw)
      have henlarge := mul_le_mul_of_nonneg_right hn1
        (mul_nonneg (Real.exp_pos (-γ*((N k : ℝ)+1))).le hq.le)
      exact hsharp.trans (by simpa only [one_mul, mul_assoc] using henlarge)
    · have hbzero : act.bid = 0 := le_antisymm (le_of_not_gt hb) act.bid_nonneg
      have hrankzero : a ≤ alphaGt (Γ k) j 0 := by
        simpa only [hbzero] using hrank j
      have hmasszero : ρ-η ≤ (userLaw (Γ k)).real (aboveAt l 0 \ aboveAt j 0) :=
        hmassk.2 j l hjl 0 (sub_nonneg.mpr hgw.le)
      have htail := ppi_rank_pair_le_exp_of_mass_and_rank (Γ k) hc hcN
        ρ a η t γ h.ratio_lt_one ha (by linarith) ht.le
        (hrows k).capacity_exact hγeq (i k) j l 0 hrankzero (hslack1 j) hmasszero
      have hzero := (ppi_zero_pair_le_rank_pair (Γ k) (hrows k).ppi
        (hrows k).feasible_continuations (i k) j l).trans htail
      have hden := ppi_zero_rank_le_n_actual_mean_of_bestResponse (Γ k) hn0
        (hrows k).ppi (hrows k).feasible_continuations (hrows k).positive_visible
        (i k) j v hvk act hact
      calc
        ppiPairProb (Γ k) (i k) act.bid j l = ppiPairProb (Γ k) (i k) 0 j l := by
          rw [hbzero]
        _ ≤ Real.exp (-γ*((N k : ℝ)+1))*binomBelow (N k) (alphaGt (Γ k) j 0) (C k) :=
          hzero
        _ ≤ Real.exp (-γ*((N k : ℝ)+1))*((n : ℝ)*meanAcceptProb (Γ k) (i k) act.bid) :=
          mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
        _ = ((n : ℝ)*Real.exp (-γ*((N k : ℝ)+1)))*meanAcceptProb (Γ k) (i k) act.bid := by
          ring
  have hrent := ppi_net_rent_uniform (Γ k) (hrows k).ppi
    (hrows k).feasible_continuations (hrows k).positive_visible (hrows k).equilibrium.users
    hc hcN (i k) j0 vstar V dk δ hδ (hslack j0) v hvk
    (hvw.trans (hw.le.trans d.cutoff_mem.2.le)) act hact
  have hrent' : R*(v-g)/((N k : ℝ)+1) ≤ v-g-act.bid := by
    have hid : R*(v-g)/((N k : ℝ)+1) =
        ppiSubcutoffTheta δ dk.upper V*(v-g)/
          (2*(n : ℝ)^2*Real.exp 1*((N k : ℝ)+1)) := by
      dsimp only [R, θ, dk, PPISubcutoffDensity.changeMeasure]
      have hm : (N k : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
      field_simp [hm, hnR.ne', (Real.exp_pos (1 : ℝ)).ne']
    rw [hid]
    simpa only [(hrows k).common_fee] using hrent
  exact ⟨hq, hrent', hpair⟩

private theorem ppi_positive_base_scalar_eventually
    (N : ℕ → ℕ) (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (n : ℕ) (V γ T : ℝ) (hγ : 0 < γ) (hT : 0 < T) :
    ∀ᶠ k in atTop,
      V*(n:ℝ)^2*((n:ℝ)*Real.exp (-γ*((N k:ℝ)+1))) < T/((N k:ℝ)+1) := by
  have hm : Tendsto (fun k => (N k:ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp hpop
  have hpoly : Tendsto (fun k => ((N k:ℝ)+1)*Real.exp (-γ*((N k:ℝ)+1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) γ hγ).comp hm
  have ht := hpoly.const_mul (V*(n:ℝ)^3)
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds hT)] with k hk
  apply (lt_div_iff₀ (by positivity : 0 < (N k:ℝ)+1)).mpr
  convert hk using 1
  ring

theorem ppi_positive_base_broadcast_sequence
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n:ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffPositiveBaseRow (Γ k) F g ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (i : ∀ k, Fin (N k+1)) (ζ w : ℝ) (hζ : 0 < ζ)
    (hspan : g+ζ ≤ w) (hw : w < vstar) :
    ∀ᶠ k in atTop, ∀ v ∈ Icc (g+ζ) w, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = n := by
  obtain ⟨R,γ,hR,hγ,hest⟩ := ppi_positive_base_subcutoff_estimates
    N C Γ F g ρ vstar V hg hn hρ hscarce d hcut hrows hpop i w (by linarith) hw
  have hscalar := ppi_positive_base_scalar_eventually N hpop n V γ (R*ζ)
    hγ (mul_pos hR hζ)
  filter_upwards [hest,hscalar] with k hk hsmall
  intro v hv act hact
  obtain ⟨hq,hrent,hpair⟩ := hk v (by linarith [hv.1]) hv.2 act hact
  apply ppi_positive_base_routeCount_eq_of_rent_pairs (Γ k) (by omega)
    (hrows k).ppi (hrows k).base_ppi (i k) v ζ V R
    ((n:ℝ)*Real.exp (-γ*((N k:ℝ)+1))) hζ hR
    (by simpa only [(hrows k).common_fee] using hv.1)
    (hv.2.trans (hw.le.trans d.cutoff_mem.2.le)) (by positivity) act hact hq
    (by simpa only [(hrows k).common_fee] using hrent) hsmall hpair

theorem ppi_positive_base_broadcast_uniform
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n:ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffPositiveBaseRow Γ F g ρ → ∀ i : Fin (N+1),
      ∀ v ∈ Icc (g+ζ) (vstar-ε), ∀ act : JointAction n,
      (problem Γ i).BestResponse v act → act.routeCount = n := by
  classical
  by_cases hspan : g+ζ ≤ vstar-ε
  · by_contra hnot
    push Not at hnot
    choose N C hsize Γ hrows i v hv act hact hbad using hnot
    have hpop : Tendsto (fun k => N k+1) atTop atTop :=
      tendsto_atTop_mono hsize tendsto_id
    have hevent := ppi_positive_base_broadcast_sequence N C Γ F g ρ vstar V
      hg hn hρ hscarce d hcut hrows hpop i ζ (vstar-ε) hζ hspan (by linarith)
    obtain ⟨k,hk⟩ := hevent.exists
    exact hbad k (hk (v k) (hv k) (act k) (hact k))
  · refine ⟨0, ?_⟩
    intro N c _ Γ _ _i v hv _act _hact
    exact (hspan (hv.1.trans hv.2)).elim

theorem ppi_positive_base_broadcast_uniform_mixed
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n : ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n : ℝ)*ρ)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffPositiveBaseRow Γ F g ρ → ∀ _i : Fin (N+1),
      ∀ᵐ v ∂Γ.F, v ∈ Icc (g+ζ) (vstar-ε) →
        ∀ᵐ act ∂Γ.σ v, act.routeCount = n := by
  obtain ⟨m0, hm0⟩ := ppi_positive_base_broadcast_uniform (Seed := Seed)
    F g ρ vstar V hg hn hρ hscarce d hcut ζ ε hζ hε
  refine ⟨m0, ?_⟩
  intro N c hN Γ hΓ i
  filter_upwards [hΓ.equilibrium.users i] with v hvbr hv
  filter_upwards [hvbr] with act hact
  exact hm0 N c hN Γ hΓ i v hv act hact

theorem ppi_positive_base_broadcast_joint_uniform
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n : ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n : ℝ)*ρ)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffPositiveBaseRow Γ F g ρ → ∀ _i : Fin (N+1),
      ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ∈ Icc (g+ζ) (vstar-ε) → x.2.routeCount = n := by
  obtain ⟨m0, hm0⟩ := ppi_positive_base_broadcast_uniform (Seed := Seed)
    F g ρ vstar V hg hn hρ hscarce d hcut ζ ε hζ hε
  refine ⟨m0, ?_⟩
  intro N c hN Γ hΓ i
  filter_upwards [ae_bestResponse_compProd Γ hΓ.equilibrium.users i] with x hx hv
  exact hm0 N c hN Γ hΓ i x.1 hv x.2 hx

theorem ppi_positive_base_broadcast_actual_draws_uniform
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n : ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n : ℝ)*ρ)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffPositiveBaseRow Γ F g ρ → ∀ _i : Fin (N+1),
      ∀ᵐ draw ∂userLaw Γ,
        draw.1.1 ∈ Icc (g+ζ) (vstar-ε) → draw.1.2.routeCount = n := by
  obtain ⟨m0, hm0⟩ := ppi_positive_base_broadcast_uniform (Seed := Seed)
    F g ρ vstar V hg hn hρ hscarce d hcut ζ ε hζ hε
  refine ⟨m0, ?_⟩
  intro N c hN Γ hΓ i
  have hbr : ∀ᵐ draw ∂userLaw Γ,
      (problem Γ i).BestResponse draw.1.1 draw.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_bestResponse_compProd Γ hΓ.equilibrium.users i)
  filter_upwards [hbr] with draw hdraw hv
  exact hm0 N c hN Γ hΓ i draw.1.1 hv draw.1.2 hdraw

theorem ppi_positive_base_broadcast_sequence_all_users
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n : ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n : ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffPositiveBaseRow (Γ k) F g ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ i : Fin (N k+1), ∀ v ∈ Icc (g+ζ) (vstar-ε),
      ∀ act : JointAction n, (problem (Γ k) i).BestResponse v act → act.routeCount = n := by
  obtain ⟨m0, hm0⟩ := ppi_positive_base_broadcast_uniform (Seed := Seed)
    F g ρ vstar V hg hn hρ hscarce d hcut ζ ε hζ hε
  filter_upwards [hpop.eventually (eventually_ge_atTop m0)] with k hk
  exact hm0 (N k) (C k) hk (Γ k) (hrows k)

theorem ppi_positive_base_broadcast_sequence_draft
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n:ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffPositiveBaseRow (Γ k) F g ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (i : ∀ k, Fin (N k+1)) (ζ w : ℝ) (hζ : 0 < ζ)
    (hspan : g+ζ ≤ w) (hw : w < vstar) :
    ∀ᶠ k in atTop, ∀ v ∈ Icc (g+ζ) w, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = n := by
  exact ppi_positive_base_broadcast_sequence N C Γ F g ρ vstar V hg hn hρ hscarce d hcut hrows hpop i ζ w hζ hspan hw

theorem ppi_positive_base_broadcast_uniform_draft
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (g ρ vstar V : ℝ) (hg : 0 < g) (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hscarce : (n:ℝ)*ρ < F.real (Ioi g))
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (ζ ε : ℝ) (hζ : 0 < ζ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffPositiveBaseRow Γ F g ρ → ∀ i : Fin (N+1),
      ∀ v ∈ Icc (g+ζ) (vstar-ε), ∀ act : JointAction n,
      (problem Γ i).BestResponse v act → act.routeCount = n := by
  exact ppi_positive_base_broadcast_uniform F g ρ vstar V hg hn hρ hscarce d hcut ζ ε hζ hε

end FCAppendix.Bayes
