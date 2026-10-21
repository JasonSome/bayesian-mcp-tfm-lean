import FCAppendix.Existence.NarrowPayOnceGlobalComparison
import FCAppendix.Existence.NarrowPayOnceLocalOptimal

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory CommonList PayOnce

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem integrable_row_utility_positive (beta : U.strategyBand) (w z : ℝ) (hz : 0<z) :
    Integrable (finiteRowUtility (R:=R) n c beta.val w z) (Measure.pi (fun _=>nu)) :=
  (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,continuous_finiteRowUtility U.n_ge beta.val
    beta.val.continuous (fun v=>U.lower_pos.trans_le (beta.property v).1) w z hz⟩).integrable _

theorem stationary_global_optimal_of_bounds (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (lo hi α γ θ : ℝ) (hθ : 0≤θ) (hθB : θ<U.B)
    (hband : ∀v,|beta.val v-U.B|≤θ) (hrho : density R c∈Icc lo hi)
    (hαlo : α<lo) (hαhi : α<1-hi)
    (hbid : (n:ℝ)*θ+2*U.B*(n:ℝ)^2*α<eps)
    (hγ : ∀p∈Icc (0:ℝ) 1,α≤|p-density R c| → γ ≤ successTangentGap n (density R c) p)
    (herror : 2*delta+(n:ℝ)*θ+(w0-U.B)*(n:ℝ)*(2*(n:ℝ)*θ/(U.B-θ))<w0*γ)
    (v : U.valueBand) (z : ℝ) (hz : 0<z) :
    finiteExpectedUtility (R:=R) n c nu beta.val v z≤
      finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v) := by
  by_cases hlocal : z∈Icc (U.B-eps) (U.B+eps)
  · exact U.stationary_local_optimal nu beta hroot v z hlocal
  have hfar : eps≤|z-U.B| := by
    by_contra hh
    have ha:=abs_le.mp (le_of_lt (lt_of_not_ge hh))
    apply hlocal
    constructor <;> linarith
  have hR : (0:ℝ)<R := Nat.cast_pos.mpr (by have:=U.c_pos; have:=U.c_le; omega)
  have hc1 : (1:ℝ)≤c := Nat.one_le_cast.mpr U.c_pos
  have hcR : (c:ℝ)≤R := Nat.cast_le.mpr U.c_le
  have hBw:= (referenceBid_pos_lt U.n_ge hR hc1 hcR U.w_pos).2
  let center:=(w0-U.B)*success n (density R c)
  have hupper (omega : Fin R→U.valueBand) : finiteRowUtility n c beta.val v z omega≤
      center-w0*γ+delta+(n:ℝ)*θ := by
    let p:=finiteRowMarginal n c beta.val z omega
    have hpos:∀i,0<rowBids beta.val z omega i := by
      intro i
      refine Fin.cases hz (fun j=>U.lower_pos.trans_le (beta.property (omega j)).1) i
    have hs:=kernelMarginal_spec n U.n_ge c _ hpos
    have hp:p∈Icc (0:ℝ) 1 := ⟨hs.1 0,hs.2.1 0⟩
    have hdist:=finiteRow_marginal_far U.n_ge U.c_pos U.c_le beta.val hθ hθB hband z hz omega
      lo hi α eps hrho hαlo hαhi hbid hfar
    have hgap:= (mul_le_mul_of_nonneg_left (hγ p hp hdist.le) U.w_pos.le).trans
      (reference_gap_ge_success_gap U.n_ge hR hc1 hcR U.w_pos hp)
    rw [referenceUtility_at_density U.n_ge hR] at hgap
    have hu:=finiteRow_utility_le_reference U.n_ge U.c_pos U.c_le beta.val hθ hθB hband z hz omega
      v w0 delta U.delta_nonneg (U.value_mem v)
    dsimp [center]
    nlinarith only [hgap,hu]
  have hupperE : finiteExpectedUtility (R:=R) n c nu beta.val v z≤center-w0*γ+delta+(n:ℝ)*θ := by
    have hh:=integral_mono (U.integrable_row_utility_positive nu beta v z hz)
      (integrable_const (center-w0*γ+delta+(n:ℝ)*θ)) hupper
    simpa [finiteExpectedUtility] using hh
  have hlowerE : center-delta-(w0-U.B)*(n:ℝ)*(2*(n:ℝ)*θ/(U.B-θ))≤
      finiteExpectedUtility (R:=R) n c nu beta.val v U.B := by
    have hh:=integral_mono
      (integrable_const (center-delta-(w0-U.B)*(n:ℝ)*(2*(n:ℝ)*θ/(U.B-θ))))
      (U.integrable_row_utility_positive nu beta v U.B (U.lower_pos.trans (by linarith [U.eps_pos])))
      (fun omega=>finiteRow_center_lower U.n_ge U.c_pos U.c_le beta.val hθ hθB hband omega
        v w0 delta U.delta_nonneg (U.value_mem v) hBw)
    simpa [finiteExpectedUtility] using hh
  have hcenter:=U.stationary_local_optimal nu beta hroot v U.B
    ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  linarith

end FiniteScoreControl

theorem exists_uniform_global_window {n : ℕ} (hn : 2≤n) {w0 lo hi kappa eps : ℝ}
    (hw : 0<w0) (hlo : 0<lo) (hhi : hi<1) (hk : 0<kappa) (he : 0<eps) :
    ∃deltaG : ℝ,0<deltaG ∧ ∀(R c : ℕ) (delta : ℝ)
      (U : FiniteScoreControl n R c w0 kappa eps delta),
      density R c∈Icc lo hi → delta≤deltaG →
      ∀(nu : Measure U.valueBand) [IsProbabilityMeasure nu] (beta : U.strategyBand),
      (∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0) →
      ∀(v : U.valueBand) (z : ℝ),0<z →
      finiteExpectedUtility (R:=R) n c nu beta.val v z≤
        finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v) := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega : 0<n)
  let α:=min (lo/2) (min ((1-hi)/2) (eps/(8*w0*(n:ℝ)^2)))
  have hα : 0<α := lt_min (half_pos hlo) (lt_min (by positivity) (by positivity))
  have hαlo : α<lo := (min_le_left _ _).trans_lt (by linarith)
  have hαhi : α<1-hi := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hαeps : 8*w0*(n:ℝ)^2*α≤eps := by
    have hh : α≤eps/(8*w0*(n:ℝ)^2) := (min_le_right _ _).trans (min_le_right _ _)
    have hmul:=(le_div_iff₀ (by positivity : (0:ℝ)<8*w0*(n:ℝ)^2)).mp hh
    nlinarith only [hmul]
  obtain ⟨γ,hγ,hgap⟩:=exists_uniform_success_gap hn hlo.le hhi.le hα
  let C:=(2*((n:ℝ)*firstJetBound n (kappa/2))/kappa)
  have hC : 0≤C := by dsimp [C,firstJetBound]; positivity
  let A:=(n:ℝ)+4*w0*(n:ℝ)^2/kappa
  have hA : 0≤A := by dsimp [A]; positivity
  let D:=2+A*C
  have hD : 0<D := by dsimp [D]; positivity
  let deltaG:=min (kappa/(4*(C+1)))
    (min (eps/(8*(n:ℝ)*(C+1))) (w0*γ/(4*D)))
  have hdG : 0<deltaG := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨deltaG,hdG,?_⟩
  intro R c delta U hrho hd nu _ beta hroot v z hz
  let θ:=C*delta
  have hδ:=U.delta_nonneg
  have hθ : 0≤θ := mul_nonneg hC hδ
  have hdk : delta*(4*(C+1))≤kappa :=
    (le_div_iff₀ (by positivity : (0:ℝ)<4*(C+1))).mp (hd.trans (min_le_left _ _))
  have hde : delta*(8*(n:ℝ)*(C+1))≤eps :=
    (le_div_iff₀ (by positivity : (0:ℝ)<8*(n:ℝ)*(C+1))).mp
      (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdgap : delta*(4*D)≤w0*γ :=
    (le_div_iff₀ (by positivity : (0:ℝ)<4*D)).mp
      (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hθk : θ≤kappa/4 := by dsimp [θ]; nlinarith only [hdk,hδ]
  have hθe : (n:ℝ)*θ≤eps/8 := by dsimp [θ]; nlinarith only [hde,mul_nonneg hnpos.le hδ]
  have hθB : θ<U.B := by linarith [U.bid_floor]
  have hBpos : 0<U.B := hk.trans_le U.bid_floor
  have hR : (0:ℝ)<R := Nat.cast_pos.mpr (by have:=U.c_pos; have:=U.c_le; omega)
  have hBw := (referenceBid_pos_lt hn hR (Nat.one_le_cast.mpr U.c_pos) (Nat.cast_le.mpr U.c_le) hw).2
  have hbid : (n:ℝ)*θ+2*U.B*(n:ℝ)^2*α<eps := by
    have hh:=mul_le_mul_of_nonneg_right hBw.le (show (0:ℝ)≤2*(n:ℝ)^2*α by positivity)
    nlinarith only [hh,hαeps,hθe,he]
  have hden : kappa/2≤U.B-θ := by linarith [U.bid_floor]
  have hratio : 2*(n:ℝ)*θ/(U.B-θ)≤4*(n:ℝ)*θ/kappa := by
    calc
      _ ≤2*(n:ℝ)*θ/(kappa/2) := div_le_div_of_nonneg_left (by positivity) (half_pos hk) hden
      _ =4*(n:ℝ)*θ/kappa := by field_simp; ring
  have hcost : (w0-U.B)*(n:ℝ)*(2*(n:ℝ)*θ/(U.B-θ))≤4*w0*(n:ℝ)^2*θ/kappa := by
    have h1:=mul_le_mul_of_nonneg_left hratio (mul_nonneg (sub_pos.mpr hBw).le hnpos.le)
    have h2:=mul_le_mul_of_nonneg_right (show (w0-U.B)*(n:ℝ)≤w0*(n:ℝ) by nlinarith)
      (show (0:ℝ)≤4*(n:ℝ)*θ/kappa by positivity)
    calc
      _ ≤ (w0-U.B)*(n:ℝ)*(4*(n:ℝ)*θ/kappa) := h1
      _ ≤ w0*(n:ℝ)*(4*(n:ℝ)*θ/kappa) := h2
      _ = 4*w0*(n:ℝ)^2*θ/kappa := by ring
  have herror : 2*delta+(n:ℝ)*θ+(w0-U.B)*(n:ℝ)*(2*(n:ℝ)*θ/(U.B-θ))<w0*γ := by
    have hident : 2*delta+(n:ℝ)*θ+4*w0*(n:ℝ)^2*θ/kappa=D*delta := by
      dsimp [D,A,θ]
      ring
    have hsmall : D*delta≤w0*γ/4 := by nlinarith only [hdgap]
    nlinarith only [hcost,hident,hsmall,mul_pos hw hγ]
  exact U.stationary_global_optimal_of_bounds nu beta hroot lo hi α γ θ hθ hθB
    (U.stationary_displacement nu beta hroot) hrho hαlo hαhi hbid
    (hgap _ hrho) herror v z hz

end FCAppendix.Existence.NarrowPayOnce
