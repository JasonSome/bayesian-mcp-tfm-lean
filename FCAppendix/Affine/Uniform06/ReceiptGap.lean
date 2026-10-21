import FCAppendix.Affine.Uniform06.SourceGuardGeometry
import FCAppendix.Affine.Uniform06.ActiveGraphComponent
import FCAppendix.Affine.Uniform06.ActiveLocalization

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ReceiptGap

open Set MeasureTheory LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07
open LiteralExperiment

def capFactor (i : Row) : ℝ := x i/(kappa i+xi i*x i)+1/200
def cap (i : Row) : ℝ := ActiveGraphComponent.activeBid i (cutoff i)+cutoff i/200
def threshold (i : Row) : ℝ := (1-xi i/2)*cap i

theorem kappa_eq_one_sub (i : Row) : kappa i=1-xi i := by
  cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ]

theorem early_optimizer_eq_active (i : Row) (v : ℝ) :
    ActiveLocalization.bestBid (xi i) v (entry i)=ActiveGraphComponent.activeBid i v := by
  simp only [ActiveLocalization.bestBid,ActiveGraphComponent.activeBid,kappa_eq_one_sub]

theorem cap_scaled (i : Row) : cap i=cutoff i*capFactor i := by
  have ht := cutoff_pos i
  have hd : 0 < kappa i+xi i*x i := by
    cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ,x,xQ]
  unfold cap capFactor ActiveGraphComponent.activeBid entry
  field_simp [ht.ne',hd.ne']

theorem capFactor_bounds (i : Row) : capFactor i ∈ Ioo (0:ℝ) 1 := by
  cases i <;> norm_num [capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]

theorem cap_bounds (i : Row) : 0 < cap i ∧ cap i < cutoff i := by
  rw [cap_scaled]
  refine ⟨mul_pos (cutoff_pos i) (capFactor_bounds i).1,?_⟩
  simpa using mul_lt_mul_of_pos_left (capFactor_bounds i).2 (cutoff_pos i)

theorem entry_below_cap (i : Row) : entry i < cap i := by
  rw [cap_scaled]
  have he : x i < capFactor i := by
    cases i <;> norm_num [capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
  simpa [entry,mul_comm] using mul_lt_mul_of_pos_left he (cutoff_pos i)

theorem receipt_numeric_margin (i : Row) :
    (1-xi i/2)*capFactor i+3/50 < x i ∧
      (1-xi i/2)*capFactor i <
        (match i with | .first => (65881/100000:ℝ) | .second => 63853/100000) := by
  cases i <;> norm_num [capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]

theorem receipt_entry_margin (i : Row) : threshold i+(3/50)*cutoff i < entry i := by
  have hh := mul_lt_mul_of_pos_right (receipt_numeric_margin i).1 (cutoff_pos i)
  simpa [threshold,cap_scaled,entry,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc] using hh

theorem lower_guard_above_threshold (i : Row) (g : GuardData)
    (hroot : entry i-cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ cutoff i/100) :
    threshold i+cutoff i/25 < g.multiplier-g.radius := by
  have hm := receipt_entry_margin i
  have ht := cutoff_pos i
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in

theorem positive_complement_receipt_gap (i : Row) (g : GuardData)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι) (E : Finset ι)
    (hroot : entry i-cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ cutoff i/100)
    (hε : 0 < g.margin) (hm : 0 < g.population)
    (hlo : 0 < g.multiplier-g.radius)
    (hout : ∀ k, k ∉ T.support → B k=0)
    (hα : 0 < guardAlpha (xi i) g T B)
    (hE : E.card ≤ imbalance T)
    (hp : 0 < complementMarginal (xi i) T B E j) :
    threshold i+cutoff i/25 < B j := by
  have hb : g.multiplier-g.radius < B j := by
    by_contra hn
    have hz := SourceGuardGeometry.complement_rejects_below_lower_guard (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) g T B hε hm hlo hout hα E hE j
      (le_of_not_gt hn)
    rw [hz] at hp
    exact (lt_irrefl _ hp).elim
  exact (lower_guard_above_threshold i g hroot hradius).trans hb

omit [Nonempty ι] in
theorem supported_sample_h_lower (i : Row) (g : GuardData)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι) (E : Finset ι)
    (hroot : entry i-cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ cutoff i/100)
    (hε : 0 < g.margin) (hm : 0 < g.population)
    (hlo : 0 < g.multiplier-g.radius)
    (hout : ∀ k, k ∉ T.support → B k=0)
    (hα : 0 < guardAlpha (xi i) g T B)
    (hE : E.card ≤ imbalance T)
    (hp : 0 < complementMarginal (xi i) T B E j)
    (k : ι) (hcap : B k ≤ cap i) (hfocalCap : B j ≤ cap i) :
    cutoff i/(25*xi i*cap i) ≤ 1/2-exposure (xi i) (B j) (B k) := by
  have hb := positive_complement_receipt_gap i g T B j E hroot hradius hε hm hlo hout hα hE hp
  have hh := FiniteGuards.sampled_h_gap (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) (cap_bounds i).1
    (show 0 < B j from by
      have hth : 0 ≤ threshold i := by
        unfold threshold
        apply mul_nonneg _ (cap_bounds i).1.le
        cases i <;> norm_num [xi,xiQ,etaQ]
      linarith [cutoff_pos i]) hcap hfocalCap (show 0 < cutoff i/25 from div_pos (cutoff_pos i) (by norm_num))
    (show (1-xi i/2)*cap i+cutoff i/25 ≤ B j from hb.le)
  convert! hh using 1
  ring

end FCAppendix.Affine.Uniform06.ReceiptGap
