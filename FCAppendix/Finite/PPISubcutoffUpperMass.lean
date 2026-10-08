import FCAppendix.Finite.PPISubcutoffDensity
import FCAppendix.Finite.PPINonrare

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_visible_slack_and_one_sided_mass
    (Γ : FiniteGame m n c Seed) (hn : 0 < n) (u w : ℝ) (_hw : 0 ≤ w)
    (hupper : ∀ᵐ d ∂userLaw Γ, u < d.1.1 →
      d.1.2.routeCount = 1 ∧ w < d.1.2.bid) :
    (∀ j, alphaGt Γ j 0 ≤ 1-(1-1/(n:ℝ))*Γ.F.real (Ioi u)) ∧
    (∀ j l : Fin n, j ≠ l → ∀ b : ℝ, b ≤ w →
      Γ.F.real (Ioi u)/(n:ℝ) ≤
        (userLaw Γ).real (aboveAt l b \ aboveAt j b)) := by
  classical
  let E : Set (ℝ × JointAction n) := {x | u < x.1}
  let R : Fin n → Set (Equiv.Perm (Fin n)) := fun j => {τ | j ∈ firstK τ 1}
  have hR (j : Fin n) : MeasurableSet (R j) := MeasurableSet.of_discrete
  have hE : (Γ.F ⊗ₘ Γ.σ) E = Γ.F (Ioi u) := by
    calc
      _ = (Γ.F ⊗ₘ Γ.σ).fst (Ioi u) := by
        rw [Measure.fst, Measure.map_apply measurable_fst measurableSet_Ioi]
        rfl
      _ = _ := by rw [Measure.fst_compProd]
  have hRm (j : Fin n) : (permLaw n).real (R j) = 1/(n:ℝ) := by
    simpa only [R, Nat.cast_one] using permLaw_mem_firstK n 1 hn hn j
  have hprod (T : Set (Equiv.Perm (Fin n))) :
      (userLaw Γ).real (E ×ˢ T) = Γ.F.real (Ioi u)*(permLaw n).real T := by
    simp only [Measure.real, userLaw, Measure.prod_prod, ENNReal.toReal_mul, hE]
  constructor
  · intro j
    have hsub : E ×ˢ (R j)ᶜ ≤ᵐ[userLaw Γ] (aboveAt j 0)ᶜ := by
      filter_upwards [hupper] with d hd hmem hac
      have hk := (hd hmem.1).1
      exact hmem.2 (by simpa only [R, Set.mem_setOf_eq, hk] using hac.1)
    have hm := ENNReal.toReal_mono (measure_ne_top (userLaw Γ) ((aboveAt j 0)ᶜ))
      (measure_mono_ae hsub)
    change (userLaw Γ).real (E ×ˢ (R j)ᶜ) ≤ (userLaw Γ).real ((aboveAt j 0)ᶜ) at hm
    rw [hprod, probReal_compl_eq_one_sub (hR j), hRm,
      probReal_compl_eq_one_sub (measurableSet_aboveAt j 0)] at hm
    change _ ≤ 1-alphaGt Γ j 0 at hm
    linarith
  · intro j l hjl b hbw
    have hsub : E ×ˢ R l ≤ᵐ[userLaw Γ] aboveAt l b \ aboveAt j b := by
      filter_upwards [hupper] with d hd hmem
      obtain ⟨hk,hbid⟩ := hd hmem.1
      refine ⟨⟨?_, hbw.trans_lt hbid⟩, ?_⟩
      · simpa only [R, Set.mem_setOf_eq, hk] using hmem.2
      · intro hj
        have hl : l ∈ firstK d.2 1 := hmem.2
        have hj' : j ∈ firstK d.2 1 := by simpa only [hk] using hj.1
        have hvalj : (d.2 j).val = 0 := by
          have hh := (mem_firstK d.2 1 j).mp hj'
          omega
        have hvall : (d.2 l).val = 0 := by
          have hh := (mem_firstK d.2 1 l).mp hl
          omega
        exact hjl (d.2.injective (Fin.ext (hvalj.trans hvall.symm)))
    have hm := ENNReal.toReal_mono
      (measure_ne_top (userLaw Γ) (aboveAt l b \ aboveAt j b)) (measure_mono_ae hsub)
    change (userLaw Γ).real (E ×ˢ R l) ≤ _ at hm
    rwa [hprod,hRm,mul_one_div] at hm

namespace NearPPIAssumptions
variable {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k+1) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
  {ρ vstar : ℝ} {a : ℕ → ℝ}

theorem ppi_upper_one_route_uniform
    (h : NearPPIAssumptions (fun k => N k+1) C Γ F 0 a ρ vstar)
    (i : ∀ k, Fin (N k+1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (u V w : ℝ) (hu : vstar < u) (hUV : u ≤ V) (hw : w < vstar) :
    ∀ᶠ k in atTop, ∀ v ∈ Icc u V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
        act.routeCount = 1 ∧ w < act.bid := by
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let z := (vstar+u)/2
  let e := (u-vstar)/8
  have he : 0 < e := by dsimp [e]; linarith
  have hz : vstar < z := by dsimp [z]; linarith
  have hzu : z < u := by dsimp [z]; linarith
  have hε : 0 < 1/(2*(n:ℝ)) := by positivity
  have hU := (Metric.tendstoUniformlyOn_iff.mp
    (h.utility_uniformOn_compact i (K := Icc z V) isCompact_Icc)) e he
  have hr := h.ppi_nonrare_one_route_uniform_on_compact i hA
    (V := Icc u V) isCompact_Icc _ hε
  have hb := h.ppi_nonrare_bids_uniform_on_compact i hA
    (V := Icc u V) isCompact_Icc _ hε ((vstar-w)/2) (by linarith)
  filter_upwards [hU,hr,hb] with k hUk hrk hbk
  intro v hv act hact
  have hvz : z ≤ v := hzu.le.trans hv.1
  have hvstar : 0 ≤ v-vstar := by linarith [hv.1]
  have hvU := hUk v ⟨hvz,hv.2⟩
  have hzU := hUk z ⟨le_rfl,hzu.le.trans hUV⟩
  rw [Real.dist_eq, max_eq_left hvstar] at hvU
  rw [Real.dist_eq, max_eq_left (sub_nonneg.mpr hz.le)] at hzU
  have hline := (problem (Γ k) (i k)).supporting_line v act hact z
  have hS : 1/2 ≤ ((problem (Γ k) (i k)).outcome act).success := by
    have hvlo := (abs_lt.mp hvU).1
    have hvhi := (abs_lt.mp hvU).2
    have hzlo := (abs_lt.mp hzU).1
    have hzhi := (abs_lt.mp hzU).2
    by_contra hh
    have hslt : ((problem (Γ k) (i k)).outcome act).success < 1/2 := lt_of_not_ge hh
    have hprod := mul_lt_mul_of_pos_left hslt (sub_pos.mpr (hzu.trans_le hv.1))
    have huv : u ≤ v := hv.1
    dsimp only [z,e] at *
    nlinarith
  have hSpos : 0 < ((problem (Γ k) (i k)).outcome act).success := by linarith
  have hk := route_pos_of_success_pos (Γ k) (i k) act hSpos
  have hrank : 1/(2*(n:ℝ)) ≤ binomBelow (N k) (alphaGt (Γ k) j act.bid) (C k) := by
    have hs := success_le_n_meanAcceptProb (Γ k) hn (i k) act
    have hq := ppi_meanAcceptProb_le_rank (Γ k) (hA k)
      (h.feasible_continuations k) (i k) j act.bid act.bid_nonneg
    simp only [Nat.add_sub_cancel] at hq
    have hmul := mul_le_mul_of_nonneg_left hq hnR.le
    apply (div_le_iff₀ (by positivity : 0 < 2*(n:ℝ))).mpr
    nlinarith
  have hbk' := hbk v hv act hact hk hrank
  simp only [sub_zero] at hbk'
  refine ⟨hrk v hv act hact hk hrank, ?_⟩
  have hab := (abs_lt.mp hbk').1
  linarith

theorem ppi_upper_draws_eventually
    (h : NearPPIAssumptions (fun k => N k+1) C Γ F 0 a ρ vstar)
    (i : ∀ k, Fin (N k+1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (V : ℝ) (hsupport : ∀ᵐ v ∂F, v ∈ Icc 0 V)
    (u w : ℝ) (hu : vstar < u) (hUV : u < V) (hw : w < vstar) :
    ∀ᶠ k in atTop, ∀ᵐ d ∂userLaw (Γ k), u < d.1.1 →
      d.1.2.routeCount = 1 ∧ w < d.1.2.bid := by
  filter_upwards [h.ppi_upper_one_route_uniform i hA u V w hu hUV.le hw] with k hk
  have hbr : ∀ᵐ d ∂userLaw (Γ k),
      (problem (Γ k) (i k)).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_bestResponse_compProd (Γ k) (h.equilibria k).users (i k))
  have hpres : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw (Γ k)) F :=
    ⟨measurable_fst.comp measurable_fst, (userLaw_value_map (Γ k)).trans (h.common_values k)⟩
  filter_upwards [hbr,hpres.quasiMeasurePreserving.ae hsupport] with d hd hds huv
  exact hk d.1.1 ⟨huv.le,hds.2⟩ d.1.2 hd

theorem ppi_subcutoff_mass_bounds
    (h : NearPPIAssumptions (fun k => N k+1) C Γ F 0 a ρ vstar)
    (i : ∀ k, Fin (N k+1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (V : ℝ) (d : PPISubcutoffDensity F vstar V)
    (w η : ℝ) (hw0 : 0 ≤ w) (hw : w < vstar) (hη : 0 < η) :
    ∀ᶠ k in atTop,
      (∀ j, alphaGt (Γ k) j 0 ≤ 1-((n:ℝ)-1)*(ρ-η)) ∧
      (∀ j l : Fin n, j ≠ l → ∀ b : ℝ, b ≤ w →
        ρ-η ≤ (userLaw (Γ k)).real (aboveAt l b \ aboveAt j b)) := by
  have hn : 0 < n := by have hh := h.proposers_two; omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨u,hu,huV,hmass⟩ := d.exists_upper_threshold n hn ρ η hη h.efficient_cutoff
  filter_upwards [h.ppi_upper_draws_eventually i hA V d.supported u w hu huV hw] with k hk
  obtain ⟨hslack,hpair⟩ := ppi_visible_slack_and_one_sided_mass (Γ k) hn u w hw0 hk
  have hmass' : (n:ℝ)*(ρ-η) ≤ (Γ k).F.real (Ioi u) := by
    simpa only [h.common_values k] using hmass.le
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf : 0 ≤ 1-1/(n:ℝ) := by
    have hh : 1/(n:ℝ) ≤ 1 := (div_le_one hnR).mpr hn1
    linarith
  have hiden : (1-1/(n:ℝ))*((n:ℝ)*(ρ-η)) = ((n:ℝ)-1)*(ρ-η) := by
    field_simp [hnR.ne']
  constructor
  · intro j
    have hh := mul_le_mul_of_nonneg_left hmass' hf
    rw [hiden] at hh
    exact (hslack j).trans (by linarith)
  · intro j l hjl b hb
    apply le_trans _ (hpair j l hjl b hb)
    exact (le_div_iff₀ hnR).mpr (by nlinarith [hmass'])

end NearPPIAssumptions
end FCAppendix.Bayes
