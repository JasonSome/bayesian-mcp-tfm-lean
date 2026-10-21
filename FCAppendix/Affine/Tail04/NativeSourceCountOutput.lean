import FCAppendix.Affine.Tail04.NativeSourceExceptionalCounts
import FCAppendix.Affine.Hybrid.Native02.CountsFromPayoff
import FCAppendix.Affine.Hybrid.Native02.SourceFamilyEstimates
import FCAppendix.Affine.Hybrid.Native02.SourceFamilyService

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourceCountOutput
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 Hybrid.Native02.FullContext

variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

lemma demand_eq_exposure (k : ℕ) (b : ℝ) (hb : b ∈ Icc p.L p.U) :
    EqualCapacity.demand p.xi b (S.price k) = exposure p.xi (S.price k) b := by
  have hq := S.finite_exposure_mem k b hb
  change max 0 (min 1 (exposure p.xi (S.price k) b)) = _
  rw [min_eq_right hq.2,max_eq_right hq.1]

theorem eventually_boxed_count_zero (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ k in atTop,∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.bid ∈ Icc p.L p.U → act.routeCount = 2 →
      |((problem (S.game k) i).outcome act).mass 0-
        (1-p.z)*(1-EqualCapacity.demand p.xi act.bid (S.price k))^2| < eps := by
  let K := countTestErrorConstant p.eta p.L
  have hK : 0 < K := by
    dsimp only [K,countTestErrorConstant]
    have hL := p.L_pos
    have he := p.eta_pos
    positivity
  let e := eps/(K+1)
  have he : 0 < e := div_pos heps (by linarith only [hK])
  have heq : (K+1)*e=eps := by dsimp only [e];field_simp
  have hKe : K*e < eps := by nlinarith only [heq,he]
  filter_upwards [S.eventually_boxed_menus_at_price 1 (by norm_num) e he] with k hk
  intro i act hb hroute
  let q := exposure p.xi (S.price k) act.bid
  have hq := S.finite_exposure_mem k act.bid hb
  let Q := activeLimitLaw p.z q p.z_nonneg p.z_lt_one.le hq.1 hq.2
  have hQ (v : ℝ) : Q.utility v act.bid 0
      (Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le) (Schedule.once 2)=
        broadcastReference p.eta p.xi p.z v (S.price k) act.bid :=
    activeLimitLaw_utility p.z q p.eta v act.bid p.z_nonneg p.z_lt_one.le
      hq.1 hq.2 p.eta_pos.le p.eta_lt_one.le
  have h0 := ((hk i act hb 0 (by norm_num)).1 hroute).le
  have h1 := ((hk i act hb 1 (by norm_num)).1 hroute).le
  rw [←hQ 0] at h0
  rw [←hQ 1] at h1
  have herr := native_count_mass_error_of_two_payoff_tests (S.game k) i p.eta p.L e
    p.eta_pos p.eta_lt_one.le p.L_pos he.le rfl rfl act hb.1 Q h0 h1 0
  have hzero : Q.mass 0 = (1-p.z)*(1-q)^2 := by
    rw [two_count_zero_mass,activeLimitLaw_success]
    ring
  rw [hzero] at herr
  rw [demand_eq_exposure S k act.bid hb]
  exact herr.trans_lt hKe

theorem common_count_error :
    ∃ err : ℕ → ℝ,(∀ k,0 < err k) ∧ Tendsto err atTop (nhds 0) ∧
      ∀ᶠ k in atTop,∀ (i : Fin (S.M k)) (act : JointAction 2),act.routeCount = 2 →
        (act.bid ∈ Icc p.L p.U →
          |((problem (S.game k) i).outcome act).mass 0-
            (1-p.z)*(1-EqualCapacity.demand p.xi act.bid (S.price k))^2| < err k) ∧
        (p.d < act.bid → act.bid < p.R → act.bid ∉ Icc p.L p.U →
          |((problem (S.game k) i).outcome act).mass 0-
            (1-EqualCapacity.demand p.xi act.bid (S.price k))^2| < err k) ∧
        (act.bid ≤ p.d →
          |((problem (S.game k) i).outcome act).mass 0-1| < err k) := by
  refine exists_positive_null_error_of_eventually (fun k eps =>
    ∀ (i : Fin (S.M k)) (act : JointAction 2),act.routeCount = 2 →
      (act.bid ∈ Icc p.L p.U →
        |((problem (S.game k) i).outcome act).mass 0-
          (1-p.z)*(1-EqualCapacity.demand p.xi act.bid (S.price k))^2| < eps) ∧
      (p.d < act.bid → act.bid < p.R → act.bid ∉ Icc p.L p.U →
        |((problem (S.game k) i).outcome act).mass 0-
          (1-EqualCapacity.demand p.xi act.bid (S.price k))^2| < eps) ∧
      (act.bid ≤ p.d → |((problem (S.game k) i).outcome act).mass 0-1| < eps)) ?_
  intro eps heps
  obtain ⟨e,he0,he,hevent⟩ := S.exists_low_service_error
  have hsmall := he.eventually (Iio_mem_nhds heps)
  filter_upwards [eventually_boxed_count_zero S eps heps,
    NativeSourceExceptionalCounts.eventually_exceptional_count_zero S eps heps,
    hevent,hsmall] with k hbox hex hlo hsm
  intro i act hk
  refine ⟨fun hb => hbox i act hb hk,fun hd hR hout => hex i act hd hR hout hk,?_⟩
  intro hb
  have hs := hlo i act hb
  rw [two_count_zero_mass]
  have hid : |(1-((problem (S.game k) i).outcome act).success)-1| =
      ((problem (S.game k) i).outcome act).success := by
    rw [show (1-((problem (S.game k) i).outcome act).success)-1 =
      -((problem (S.game k) i).outcome act).success by ring,
      abs_neg,abs_of_nonneg ((problem (S.game k) i).outcome act).success_nonneg]
  rw [hid]
  exact hs.trans_lt hsm

end FCAppendix.Affine.Tail04.NativeSourceCountOutput
