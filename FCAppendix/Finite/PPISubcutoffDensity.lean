import FCAppendix.Finite.PPIRentBound
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

structure PPISubcutoffDensity (F : Measure ℝ) (vstar V : ℝ) where
  density : ℝ → ℝ
  measurable_density : Measurable density
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  cutoff_mem : vstar ∈ Ioo 0 V
  supported : ∀ᵐ v ∂F, v ∈ Icc 0 V
  density_eq : F.restrict (Icc 0 V) =
    (volume.withDensity (fun v => ENNReal.ofReal (density v))).restrict (Icc 0 V)
  density_lower : ∀ v ∈ Icc 0 V, lower ≤ density v
  density_upper : ∀ v ∈ Icc 0 V, density v ≤ upper
  continuous_density : ContinuousOn density (Icc 0 V)
  locally_C1 : ∃ U : Set ℝ, IsOpen U ∧ vstar ∈ U ∧ U ⊆ Ioo 0 V ∧
    ContDiffOn ℝ 1 density U

namespace PPISubcutoffDensity
variable {F : Measure ℝ} {vstar V : ℝ}

def changeMeasure (d : PPISubcutoffDensity F vstar V) (F' : Measure ℝ)
    (hF : F' = F) : PPISubcutoffDensity F' vstar V where
  density := d.density
  measurable_density := d.measurable_density
  lower := d.lower
  upper := d.upper
  lower_pos := d.lower_pos
  upper_pos := d.upper_pos
  cutoff_mem := d.cutoff_mem
  supported := by simpa only [hF] using d.supported
  density_eq := by simpa only [hF] using d.density_eq
  density_lower := d.density_lower
  density_upper := d.density_upper
  continuous_density := d.continuous_density
  locally_C1 := d.locally_C1

lemma measure_eq_lintegral (d : PPISubcutoffDensity F vstar V)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Icc 0 V) :
    F E = ∫⁻ x in E, ENNReal.ofReal (d.density x) := by
  have he : F.restrict E =
      (volume.withDensity (fun x => ENNReal.ofReal (d.density x))).restrict E := by
    rw [← Measure.restrict_restrict_of_subset hsub, d.density_eq,
      Measure.restrict_restrict_of_subset hsub]
  have he' := congrArg (fun μ : Measure ℝ => μ univ) he
  simpa only [Measure.restrict_apply_univ, withDensity_apply _ hE] using he'

lemma measure_le_upper (d : PPISubcutoffDensity F vstar V)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Icc 0 V) :
    F E ≤ ENNReal.ofReal d.upper * volume E := by
  rw [d.measure_eq_lintegral E hE hsub]
  calc
    _ ≤ ∫⁻ _x in E, ENNReal.ofReal d.upper := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with x hx
      exact ENNReal.ofReal_le_ofReal (d.density_upper x (hsub hx))
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]

lemma interval_mass_pos [IsFiniteMeasure F] (d : PPISubcutoffDensity F vstar V)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ V) :
    0 < F.real (Ioo a b) := by
  have hsub : Ioo a b ⊆ Icc 0 V := fun x hx =>
    ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩
  have hm : 0 < F (Ioo a b) := by
    rw [d.measure_eq_lintegral _ measurableSet_Ioo hsub]
    apply (setLIntegral_pos_iff d.measurable_density.ennreal_ofReal).mpr
    have he : Function.support (fun x => ENNReal.ofReal (d.density x)) ∩ Ioo a b =
        Ioo a b := by
      apply inter_eq_right.mpr
      intro x hx
      exact (ENNReal.ofReal_pos.mpr
        (d.lower_pos.trans_le (d.density_lower x (hsub hx)))).ne'
    rw [he, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)

lemma interval_mass_le [IsFiniteMeasure F] (d : PPISubcutoffDensity F vstar V)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ V) :
    F.real (Ioo a b) ≤ d.upper * (b-a) := by
  have hh := d.measure_le_upper (Ioo a b) measurableSet_Ioo
    (fun x hx => ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩)
  rw [Real.volume_Ioo, ← ENNReal.ofReal_mul d.upper_pos.le] at hh
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (mul_nonneg d.upper_pos.le (sub_nonneg.mpr hab))] using ht

lemma interval_mass_le_Ioc [IsFiniteMeasure F] (d : PPISubcutoffDensity F vstar V)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ V) :
    F.real (Ioc a b) ≤ d.upper * (b-a) := by
  have hh := d.measure_le_upper (Ioc a b) measurableSet_Ioc
    (fun x hx => ⟨ha.trans hx.1.le, hx.2.trans hb⟩)
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul d.upper_pos.le] at hh
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (mul_nonneg d.upper_pos.le (sub_nonneg.mpr hab))] using ht

theorem nullSingletonClass (d : PPISubcutoffDensity F vstar V) : NullSingletonClass F := by
  constructor
  intro x
  by_cases hx : x ∈ Icc 0 V
  · have hh := d.measure_le_upper {x} (measurableSet_singleton x)
      (singleton_subset_iff.mpr hx)
    simpa only [measure_singleton, mul_zero, nonpos_iff_eq_zero] using hh
  · have hz : F ((Icc 0 V)ᶜ) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [d.supported] with v hv hvc
      exact hvc hv
    exact measure_mono_null (singleton_subset_iff.mpr hx) hz

lemma local_density (d : PPISubcutoffDensity F vstar V) :
    ∃ (f : ℝ → ℝ) (U : Set ℝ), Measurable f ∧ MeasurableSet U ∧ U ∈ 𝓝 vstar ∧
      F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U ∧
      ContinuousAt f vstar ∧ 0 < f vstar := by
  have hnh : Icc (0:ℝ) V ∈ 𝓝 vstar :=
    Icc_mem_nhds d.cutoff_mem.1 d.cutoff_mem.2
  exact ⟨d.density, Icc 0 V, d.measurable_density, measurableSet_Icc, hnh,
    d.density_eq,
    (d.continuous_density vstar ⟨d.cutoff_mem.1.le,d.cutoff_mem.2.le⟩).continuousAt hnh,
    d.lower_pos.trans_le (d.density_lower vstar
      ⟨d.cutoff_mem.1.le,d.cutoff_mem.2.le⟩)⟩

theorem exists_upper_threshold [IsFiniteMeasure F]
    (d : PPISubcutoffDensity F vstar V) (n : ℕ) (hn : 0 < n)
    (ρ η : ℝ) (hη : 0 < η) (hcut : F.real (Ioi vstar) = (n:ℝ)*ρ) :
    ∃ u, vstar < u ∧ u < V ∧ (n:ℝ)*(ρ-η) < F.real (Ioi u) := by
  have hupper : 0 < d.upper := d.upper_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let z := min ((V-vstar)/2) ((n:ℝ)*η/(2*d.upper))
  have hz : 0 < z := lt_min (by linarith [d.cutoff_mem.2]) (by positivity)
  have hzV : z ≤ (V-vstar)/2 := min_le_left _ _
  have hzm : z ≤ (n:ℝ)*η/(2*d.upper) := min_le_right _ _
  have huV : vstar+z < V := by linarith [d.cutoff_mem.2]
  refine ⟨vstar+z, by linarith, huV, ?_⟩
  have hm := d.interval_mass_le_Ioc vstar (vstar+z) d.cutoff_mem.1.le
    (by linarith) huV.le
  have he : F.real (Ioc vstar (vstar+z)) =
      F.real (Ioi vstar)-F.real (Ioi (vstar+z)) := by
    rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi (by linarith)) measurableSet_Ioi]
  rw [he, hcut] at hm
  have hzbound : d.upper*z ≤ (n:ℝ)*η/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*d.upper)).mp hzm
    nlinarith
  have hnη : 0 < (n:ℝ)*η := mul_pos (Nat.cast_pos.mpr hn) hη
  nlinarith
end PPISubcutoffDensity

variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem visibleBidMeasure_singleton_of_full_atomlessness
    (Γ : FiniteGame (N+1) n c Seed) (h : VisibleAtomless Γ) (j : Fin n) (b : ℝ) :
    visibleBidMeasure Γ j {b} = 0 := by
  have hm : Measurable (fun d : UserDraw n => d.1.2.bid) := by
    simpa only [Function.comp_def] using (measurable_bid n).comp
      (measurable_snd.comp (measurable_fst : Measurable
        (Prod.fst : UserDraw n → ℝ × JointAction n)))
  unfold visibleBidMeasure
  rw [Measure.map_apply hm (measurableSet_singleton b),
    Measure.restrict_apply (hm (measurableSet_singleton b))]
  convert h j b using 2
  ext d
  simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_setOf_eq]
  exact and_comm

theorem exists_actual_draw_in_value_band (Γ : FiniteGame (N+1) n c Seed)
    (a b : ℝ) (hmass : 0 < Γ.F.real (Ioo a b))
    (P : UserDraw n → Prop) (hP : ∀ᵐ d ∂userLaw Γ, P d) :
    ∃ d : UserDraw n, d.1.1 ∈ Ioo a b ∧ P d := by
  have he : (userLaw Γ) {d : UserDraw n | d.1.1 ∈ Ioo a b} = Γ.F (Ioo a b) := by
    have hm : Measurable (fun d : UserDraw n => d.1.1) :=
      measurable_fst.comp measurable_fst
    rw [← userLaw_value_map Γ, Measure.map_apply hm measurableSet_Ioo]
    rfl
  have hz : (userLaw Γ) {d : UserDraw n | d.1.1 ∈ Ioo a b} ≠ 0 := by
    rw [he]
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hmass
    exact lt_irrefl _ hmass
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hz (ae_restrict_of_ae hP)

lemma ppi_payoff_zero_fee (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0) (i : Fin (N+1))
    (v : ℝ) (act : JointAction n) :
    (problem Γ i).payoff v act =
      v*((problem Γ i).outcome act).success-act.bid*((problem Γ i).outcome act).load := by
  change ((problem Γ i).outcome act).utility v act.bid Γ.g Γ.A Γ.G = _
  rw [CountLaw.utility_eq,hA,hg,CountLaw.charge_ppi]
  ring

theorem ppi_positive_bestResponse_of_visible_slack
    (Γ : FiniteGame (N+1) n c Seed) (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (hc : 0 < c) (i : Fin (N+1)) (j : Fin n)
    (hslack : alphaGt Γ j 0 < 1) (v : ℝ) (hv : 0 < v)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    0 < ((problem Γ i).outcome act).success ∧ 1 ≤ act.routeCount ∧ act.bid < v := by
  have hQ := binomBelow_pos_of_lt_one N c hc _ measureReal_nonneg hslack
  have hS := ppi_success_ge_zero_rank Γ hA hj hatom i j v hv act
    (by simpa only [hg,zero_add] using hact)
  have hs := hQ.trans_le hS
  have hU := ppi_envelope_ge_zero_rank Γ hA hj hatom i j v
  simp only [hg,zero_add] at hU
  have hUpos : 0 < (problem Γ i).envelope v := (mul_pos hv hQ).trans_le hU
  have hp := (problem Γ i).bestResponse_iff_attains v act |>.mp hact
  rw [ppi_payoff_zero_fee Γ hA hg i v act] at hp
  have hL := ((problem Γ i).outcome act).success_le_load
  have hcost := mul_le_mul_of_nonneg_left hL act.bid_nonneg
  have hbs : 0 < (v-act.bid)*((problem Γ i).outcome act).success := by nlinarith
  exact ⟨hs, route_pos_of_success_pos Γ i act hs,
    sub_pos.mp (pos_of_mul_pos_left hbs hs.le)⟩

theorem ppi_bestResponse_bid_pos_of_full_atomlessness
    (Γ : FiniteGame (N+1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (hu : UsersOptimal Γ) (hz : ∀ j, visibleBidMeasure Γ j {0} = 0)
    (hc : 0 < c) (i : Fin (N+1)) (j : Fin n) (hslack : alphaGt Γ j 0 < 1)
    (v : ℝ) (hv : 0 < v) (hband : 0 < Γ.F.real (Ioo (v/2) v))
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) : 0 < act.bid := by
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hpos := routed_bids_pos_of_visible_zero_atomless Γ hz
  obtain ⟨d, hd, hdbr, hdpos⟩ := exists_actual_draw_in_value_band Γ (v/2) v hband
    (fun d => (problem Γ i).BestResponse d.1.1 d.1.2 ∧
      (1 ≤ d.1.2.routeCount → 0 < d.1.2.bid)) (hbr.and hpos)
  have hy : 0 < d.1.1 := (half_pos hv).trans hd.1
  obtain ⟨hs,hk,_⟩ := ppi_positive_bestResponse_of_visible_slack Γ hA hg hj hatom
    hc i j hslack d.1.1 hy d.1.2 hdbr
  have hb := hdpos hk
  have horder := (problem Γ i).success_order d.1.1 v hd.2 d.1.2 act hdbr hact
  have hordermul := mul_le_mul_of_nonneg_left horder hy.le
  have hdev := hdbr act
  rw [ppi_payoff_zero_fee Γ hA hg i d.1.1 act,
    ppi_payoff_zero_fee Γ hA hg i d.1.1 d.1.2] at hdev
  have hL : 0 < ((problem Γ i).outcome d.1.2).load :=
    hs.trans_le ((problem Γ i).outcome d.1.2).success_le_load
  by_contra hnot
  have hzact : act.bid = 0 := le_antisymm (le_of_not_gt hnot) act.bid_nonneg
  rw [hzact,zero_mul,sub_zero] at hdev
  have hpaid : 0 < d.1.2.bid*((problem Γ i).outcome d.1.2).load := mul_pos hb hL
  nlinarith

def ppiSubcutoffTheta (δ fmax V : ℝ) : ℝ := min (1/2) (δ/(2*fmax*V))

theorem ppi_rent_uniform_near_zero
    (Γ : FiniteGame (N+1) n c Seed) [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hg : Γ.g = 0)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (hu : UsersOptimal Γ) (hc : 0 < c) (hcN : c ≤ N+1)
    (i : Fin (N+1)) (j : Fin n) (vstar V : ℝ)
    (d : PPISubcutoffDensity Γ.F vstar V)
    (δ : ℝ) (hδ : 0 < δ) (hslack : alphaGt Γ j 0 ≤ 1-δ)
    (v : ℝ) (hv : 0 < v) (hvV : v ≤ V)
    (act : JointAction n) (hact : (problem Γ i).BestResponse v act) :
    ppiSubcutoffTheta δ d.upper V * v /
      (2*(n:ℝ)^2*Real.exp 1*((N:ℝ)+1)) ≤ v-act.bid := by
  let θ := ppiSubcutoffTheta δ d.upper V
  let h := θ*v/((N:ℝ)+1)
  have hV : 0 < V := d.cutoff_mem.1.trans d.cutoff_mem.2
  have hupper : 0 < d.upper := d.upper_pos
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθhalf : θ ≤ 1/2 := min_le_left _ _
  have hθmass : θ ≤ δ/(2*d.upper*V) := min_le_right _ _
  have hm : 0 < (N:ℝ)+1 := by positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hhv : h ≤ v/2 := by
    dsimp [h]
    apply (div_le_iff₀ hm).mpr
    have htv := mul_le_mul_of_nonneg_right hθhalf hv.le
    have hNv := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hv.le
    nlinarith
  have hl : 0 < v-h := by linarith
  have hband := d.interval_mass_pos (v-h) (v-h/2) hl.le (by linarith) (by linarith)
  have hbr : ∀ᵐ x ∂userLaw Γ, (problem Γ i).BestResponse x.1.1 x.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  obtain ⟨x,hx,hxbr⟩ := exists_actual_draw_in_value_band Γ _ _ hband _ hbr
  have hy0 : 0 < x.1.1 := hl.trans hx.1
  have hyv : x.1.1 < v := by linarith [hx.2]
  have hmass := d.interval_mass_le x.1.1 v hy0.le hyv.le hvV
  have hNv : (N:ℝ)/((N:ℝ)+1) ≤ 1 := (div_le_one hm).mpr (by linarith)
  have hθfv : θ*d.upper*v ≤ δ := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 2*d.upper*V)).mp hθmass
    have hvbound := mul_le_mul_of_nonneg_left hvV (mul_nonneg hθ.le d.upper_pos.le)
    nlinarith
  have hNh : (N:ℝ)*d.upper*h ≤ δ := by
    dsimp only [h]
    have hprod := mul_le_mul_of_nonneg_left hNv
      (mul_nonneg (mul_nonneg hθ.le d.upper_pos.le) hv.le)
    have hid : θ*d.upper*v*((N:ℝ)/((N:ℝ)+1)) =
        (N:ℝ)*d.upper*(θ*v/((N:ℝ)+1)) := by ring
    rw [hid] at hprod
    linarith
  have hsmall : (N:ℝ)/δ*Γ.F.real (Ioo x.1.1 v) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hδ).mpr
    have hM := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N)
    have hyh : v-x.1.1 ≤ h := by linarith [hx.1]
    have hM' := mul_le_mul_of_nonneg_left hyh
      (mul_nonneg (Nat.cast_nonneg N) d.upper_pos.le)
    have hh' : (N:ℝ)*Γ.F.real (Ioo x.1.1 v) ≤ δ := by nlinarith
    simpa only [one_mul] using hh'
  have hrent := (ppi_rent_of_small_value_band Γ hA hg hj hatom hu hc hcN i j
    δ hδ hslack x.1.1 v hy0 hyv x.1.2 act hxbr hact hsmall).2
  have hden : 0 < (n:ℝ)^2*Real.exp 1 := by
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    positivity
  have hcomp := div_le_div_of_nonneg_right
    (show h/2 ≤ v-x.1.1 by linarith [hx.2]) hden.le
  apply le_trans _ (hcomp.trans hrent)
  change θ*v/(2*(n:ℝ)^2*Real.exp 1*((N:ℝ)+1)) ≤ _
  dsimp only [h]
  apply le_of_eq
  field_simp [hm.ne', hden.ne']

end FCAppendix.Bayes
