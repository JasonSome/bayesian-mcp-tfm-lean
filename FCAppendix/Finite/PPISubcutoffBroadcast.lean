import FCAppendix.Finite.PPISubcutoffRank
import FCAppendix.Finite.PPISubcutoffDeviation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure PPISubcutoffRow {N c : ℕ} (Γ : FiniteGame (N+1) n c Seed)
    (F : Measure ℝ) (ρ : ℝ) : Prop where
  common_values : Γ.F = F
  zero_fee : Γ.g = 0
  ppi : Γ.A = Schedule.ppi n
  capacity_exact : (c:ℝ) = ρ*((N:ℝ)+1)
  equilibrium : IsAEEquilibrium Γ
  feasible_continuations : ∀ j, ProposerRationalAtFeasibleLists Γ j
  visible_atomless : VisibleAtomless Γ
  policy_symmetry : PolicyLawEquivariant Γ

namespace PPISubcutoffRow
variable {N c : ℕ} {Γ : FiniteGame (N+1) n c Seed} {F : Measure ℝ} {ρ : ℝ}

lemma positive_visible (h : PPISubcutoffRow Γ F ρ) : PositiveVisibleAtomless Γ :=
  VisibleAtomless.positive Γ h.visible_atomless

lemma visible_zero (h : PPISubcutoffRow Γ F ρ) (j : Fin n) :
    visibleBidMeasure Γ j {0} = 0 :=
  visibleBidMeasure_singleton_of_full_atomlessness Γ h.visible_atomless j 0

lemma capacity_pos (h : PPISubcutoffRow Γ F ρ) (hρ : 0 < ρ) : 0 < c := by
  have hh : (0:ℝ) < c := by rw [h.capacity_exact]; positivity
  exact_mod_cast hh

lemma capacity_lt (h : PPISubcutoffRow Γ F ρ) (hρ : ρ < 1) : c < N+1 := by
  have hh := mul_lt_mul_of_pos_right hρ (show 0 < (N:ℝ)+1 by positivity)
  rw [← h.capacity_exact,one_mul] at hh
  exact_mod_cast hh
end PPISubcutoffRow

private theorem ppi_density_positive_values (F : Measure ℝ) [IsProbabilityMeasure F]
    (vstar V : ℝ) (d : PPISubcutoffDensity F vstar V) : F.real (Ioi 0) = 1 := by
  letI : NullSingletonClass F := d.nullSingletonClass
  have hz : ∀ᵐ v ∂F, v ≠ 0 := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0 : F {0} = 0))
  have he : F.real (Ioi 0) = F.real univ := by
    apply measureReal_congr
    filter_upwards [d.supported,hz] with v hv hv0
    have hp : 0 < v := lt_of_le_of_ne hv.1 hv0.symm
    exact propext ⟨fun _ => trivial, fun _ => hp⟩
  simpa only [probReal_univ] using he

theorem ppi_subcutoff_rows_nearPPI
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffRow (Γ k) F ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop) :
    NearPPIAssumptions (fun k => N k+1) C Γ F 0 (fun _ => 1) ρ vstar := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hρ1 : ρ < 1 := by nlinarith [mul_le_mul_of_nonneg_right hn1 hρ.le]
  apply CongestedAssumptions.nearPPI_of_ppi (hA := fun k => (hrows k).ppi)
  refine {
    proposers_two := hn
    capacity_lt_population := fun k => (hrows k).capacity_lt hρ1
    common_values := fun k => (hrows k).common_values
    common_fee := fun k => (hrows k).zero_fee
    ratio_pos := hρ
    ratio_lt_one := hρ1
    population_grows := hpop
    capacity_ratio := ?_
    equilibria := fun k => (hrows k).equilibrium
    feasible_continuations := fun k => (hrows k).feasible_continuations
    visible_atomless := fun k => (hrows k).positive_visible
    policy_symmetry := fun k => (hrows k).policy_symmetry
    scarcity := ?_
    efficient_cutoff := hcut
    local_density := d.local_density }
  · have he : (fun k => (C k:ℝ)/(N k+1:ℕ)) = fun _ : ℕ => ρ := by
      funext k
      rw [Nat.cast_add,Nat.cast_one,(hrows k).capacity_exact]
      field_simp
    rw [he]
    exact tendsto_const_nhds
  · rw [ppi_density_positive_values F vstar V d]
    exact hscarce

private theorem ppi_subcutoff_scalar_eventually
    (N : ℕ → ℕ) (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (n : ℕ) (Δ γ R : ℝ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hR : 0 < R) :
    ∀ᶠ k in atTop,
      (n:ℝ)*Real.exp (-Δ^2*((N k:ℝ)+1)) < 1 ∧
      (n:ℝ)^2*Real.exp (-γ*((N k:ℝ)+1)) < R/((N k:ℝ)+1) := by
  have hm : Tendsto (fun k => (N k:ℝ)+1) atTop atTop := by
    have hh : Tendsto (fun k => ((N k+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hpop
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have he : Tendsto (fun k => Real.exp (-Δ^2*((N k:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hm.const_mul_atTop (sq_pos_of_pos hΔ))
  have he' : Tendsto (fun k => (n:ℝ)*Real.exp (-Δ^2*((N k:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (n:ℝ)
  have hpoly : Tendsto (fun k => ((N k:ℝ)+1)*Real.exp (-γ*((N k:ℝ)+1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) γ hγ).comp hm
  have hpoly' : Tendsto (fun k => (n:ℝ)^2*
      (((N k:ℝ)+1)*Real.exp (-γ*((N k:ℝ)+1)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpoly.const_mul ((n:ℝ)^2)
  filter_upwards [he'.eventually (eventually_lt_nhds zero_lt_one),
    hpoly'.eventually (eventually_lt_nhds hR)] with k hk hk'
  refine ⟨hk,(lt_div_iff₀ (by positivity : 0 < (N k:ℝ)+1)).mpr ?_⟩
  nlinarith [hk']

theorem ppi_subcutoff_broadcast_sequence
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (hrows : ∀ k, PPISubcutoffRow (Γ k) F ρ)
    (hpop : Tendsto (fun k => N k+1) atTop atTop)
    (i : ∀ k, Fin (N k+1)) (w : ℝ) (hw0 : 0 ≤ w) (hw : w < vstar) :
    ∀ᶠ k in atTop, ∀ v : ℝ, 0 < v → v ≤ w → ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = n := by
  letI : NullSingletonClass F := d.nullSingletonClass
  let h := ppi_subcutoff_rows_nearPPI N C Γ F ρ vstar V hn hρ hscarce d hcut hrows hpop
  let j0 : Fin n := ⟨0,by omega⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2:ℝ) ≤ n := Nat.cast_le.mpr hn
  let astar := F.real (Ioi w)/(n:ℝ)
  let Δ := (astar-ρ)/2
  let a := ρ+Δ
  obtain ⟨haρ,ha1⟩ := ppi_value_rank_gap F vstar V d hn ρ w hw0 hw hcut
  have hΔ : 0 < Δ := by dsimp [Δ,astar]; linarith
  have hra : ρ < a := by dsimp only [a]; linarith
  have ha : a < 1 := by dsimp [a,Δ,astar]; linarith
  obtain ⟨η,t,γ,hη,hηhalf,ht,hγ,hγeq⟩ := exists_ppi_subcutoff_pair_decay ρ a hρ hra ha
  let δ := ((n:ℝ)-1)*ρ/2
  have hnminus : 0 < (n:ℝ)-1 := by linarith
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let θ := ppiSubcutoffTheta δ d.upper V
  let R := θ/(2*(n:ℝ)^2*Real.exp 1)
  have hV : 0 < V := d.cutoff_mem.1.trans d.cutoff_mem.2
  have hupper : 0 < d.upper := d.upper_pos
  have hθ : 0 < θ := by dsimp [θ,ppiSubcutoffTheta]; exact lt_min (by norm_num) (by positivity)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hmass := h.ppi_subcutoff_mass_bounds i (fun k => (hrows k).ppi) V d w η hw0 hw hη
  have hscalar := ppi_subcutoff_scalar_eventually N hpop n Δ γ R hΔ hγ hR
  filter_upwards [hmass,hscalar] with k hmassk hscalark
  let dk := d.changeMeasure (Γ k).F (hrows k).common_values
  letI : NullSingletonClass (Γ k).F := dk.nullSingletonClass
  have hc := (hrows k).capacity_pos hρ
  have hcN := ((hrows k).capacity_lt h.ratio_lt_one).le
  have hslack (j : Fin n) : alphaGt (Γ k) j 0 ≤ 1-δ := by
    have hupper := hmassk.1 j
    have hh := mul_le_mul_of_nonneg_left hηhalf.le (show 0 ≤ (n:ℝ)-1 by linarith)
    dsimp only [δ]
    nlinarith
  have hslack1 (j : Fin n) : alphaGt (Γ k) j 0 < 1 := by linarith [hslack j,hδ]
  intro v hv hvw act hact
  obtain ⟨hb,hrank0⟩ := ppi_subcutoff_rank_separation (Γ k) hn
    (hrows k).ppi (hrows k).zero_fee (hrows k).feasible_continuations
    (hrows k).positive_visible (hrows k).equilibrium.users (hrows k).visible_zero
    hc hcN ρ hρ (hrows k).capacity_exact vstar V dk w hw0 hw
    (by simpa only [(hrows k).common_values] using hcut) (i k) j0 (hslack1 j0)
    (by simpa only [Δ, astar, (hrows k).common_values] using hscalark.1) v hv hvw act hact
  have hrank : ∀ j, a ≤ alphaGt (Γ k) j act.bid := by
    intro j
    rw [alphaGt_eq (Γ k) j j0 act.bid]
    simpa only [a, Δ, astar, (hrows k).common_values] using hrank0
  have hactslack (j : Fin n) : alphaGt (Γ k) j act.bid < 1 :=
    (alphaGt_antitone (Γ k) j act.bid_nonneg).trans_lt (hslack1 j)
  have hq : 0 < meanAcceptProb (Γ k) (i k) act.bid := by
    rw [ppi_meanAcceptProb_eq_rank (Γ k) (hrows k).ppi (hrows k).positive_visible
      (hrows k).feasible_continuations (i k) j0 act.bid hb]
    exact binomBelow_pos_of_lt_one (N k) (C k) hc _ measureReal_nonneg (hactslack j0)
  have hpositive := ppi_positive_bestResponse_of_visible_slack (Γ k)
    (hrows k).ppi (hrows k).zero_fee (hrows k).feasible_continuations
    (hrows k).positive_visible hc (i k) j0 (hslack1 j0) v hv act hact
  have hbidw : act.bid ≤ w := hpositive.2.2.le.trans hvw
  have hpair : ∀ j l : Fin n, j ≠ l → ppiPairProb (Γ k) (i k) act.bid j l ≤
      Real.exp (-γ*((N k:ℝ)+1))*meanAcceptProb (Γ k) (i k) act.bid := by
    intro j l hjl
    exact ppi_pair_acceptance_le_exp_of_mass_and_rank (Γ k) (hrows k).ppi
      (hrows k).positive_visible (hrows k).feasible_continuations hc hcN
      ρ a η t γ hρ h.ratio_lt_one ha (by linarith) ht.le (hrows k).capacity_exact hγeq
      (i k) j l act.bid hb (hrank j) (hactslack j) (hmassk.2 j l hjl act.bid hbidw)
  have hrent := ppi_rent_uniform_near_zero (Γ k) (hrows k).ppi (hrows k).zero_fee
    (hrows k).feasible_continuations (hrows k).positive_visible (hrows k).equilibrium.users
    hc hcN (i k) j0 vstar V dk δ hδ (hslack j0) v hv
    (hvw.trans (hw.le.trans d.cutoff_mem.2.le)) act hact
  have hrent' : R*v/((N k:ℝ)+1) ≤ v-act.bid := by
    have hid : R*v/((N k:ℝ)+1) = ppiSubcutoffTheta δ dk.upper V*v/
        (2*(n:ℝ)^2*Real.exp 1*((N k:ℝ)+1)) := by
      dsimp only [R,θ,dk,PPISubcutoffDensity.changeMeasure]
      field_simp [hnR.ne', (Real.exp_pos (1:ℝ)).ne']
    rw [hid]
    exact hrent
  exact ppi_routeCount_eq_of_small_pair_and_rent (Γ k) (by omega)
    (hrows k).ppi (hrows k).zero_fee (i k) v hv act hact R
    (Real.exp (-γ*((N k:ℝ)+1))) (Real.exp_pos _).le hq hrent' hscalark.2 hpair

theorem ppi_broadcast_below_cutoff_uniform
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffRow Γ F ρ → ∀ (i : Fin (N+1)) (v : ℝ),
      0 < v → v ≤ vstar-ε → ∀ act : JointAction n,
      (problem Γ i).BestResponse v act → act.routeCount = n := by
  classical
  by_cases hw : 0 < vstar-ε
  · by_contra hnot
    push Not at hnot
    choose N C hsize Γ hrows i v hv hvw act hact hbad using hnot
    have hpop : Tendsto (fun k => N k+1) atTop atTop :=
      tendsto_atTop_mono hsize tendsto_id
    have hh := ppi_subcutoff_broadcast_sequence N C Γ F ρ vstar V hn hρ hscarce
      d hcut hrows hpop i (vstar-ε) hw.le (by linarith)
    obtain ⟨k,hk⟩ := hh.exists
    exact hbad k (hk (v k) (hv k) (hvw k) (act k) (hact k))
  · refine ⟨0,?_⟩
    intro N c _ Γ _ _i v hv hvw _act _
    exact (hw (lt_of_lt_of_le hv hvw)).elim

theorem ppi_broadcast_below_cutoff_uniform_mixed
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (ρ vstar V : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hscarce : (n:ℝ)*ρ < 1)
    (d : PPISubcutoffDensity F vstar V) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ N c : ℕ, m0 ≤ N+1 → ∀ Γ : FiniteGame (N+1) n c Seed,
      PPISubcutoffRow Γ F ρ → ∀ _i : Fin (N+1),
      ∀ᵐ v ∂Γ.F, 0 < v → v ≤ vstar-ε → ∀ᵐ act ∂Γ.σ v, act.routeCount = n := by
  obtain ⟨m0,hm0⟩ := ppi_broadcast_below_cutoff_uniform (Seed := Seed)
    F ρ vstar V hn hρ hscarce d hcut ε hε
  refine ⟨m0,?_⟩
  intro N c hN Γ hΓ i
  filter_upwards [hΓ.equilibrium.users i] with v hvbr hv hvw
  filter_upwards [hvbr] with act hact
  exact hm0 N c hN Γ hΓ i v hv hvw act hact

end FCAppendix.Bayes
