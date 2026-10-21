import FCAppendix.Affine.Hybrid.Native02.ConditionalLimits
import FCAppendix.Affine.Hybrid.Menu

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set MeasureTheory ProbabilityTheory Game Bayes Filter Topology

theorem activeLimitLaw_utility (z q eta v b : ℝ)
    (hz0 : 0≤ z) (hz1 : z≤1) (hq0 : 0≤ q) (hq1 : q≤1)
    (he0 : 0≤ eta) (he1 : eta≤1) :
    (activeLimitLaw z q hz0 hz1 hq0 hq1).utility v b 0
      (Schedule.affine 2 eta he0 he1) (Schedule.once 2)=
      z*(v-b)+(1-z)*independentTwo eta v b q := by
  rw [CountLaw.utility_eq,CountLaw.charge_affine,activeLimitLaw_success,
    activeLimitLaw_duplicates]
  unfold independentTwo
  ring

theorem utility_one_sub_zero (P : CountLaw 2) (b : ℝ) (A G : Schedule 2) :
    P.utility 1 b 0 A G-P.utility 0 b 0 A G=P.success := by
  rw [CountLaw.utility_eq,CountLaw.utility_eq]
  ring

theorem utility_zero_affine (P : CountLaw 2) (eta b : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) :
    P.utility 0 b 0 (Schedule.affine 2 eta he0 he1) (Schedule.once 2)=
      -b*(P.success+eta*P.duplicates) := by
  rw [CountLaw.utility_eq,CountLaw.charge_affine]
  ring

theorem success_error_of_two_payoff_tests (P Q : CountLaw 2) (b e : ℝ)
    (A G : Schedule 2)
    (h0 : |P.utility 0 b 0 A G-Q.utility 0 b 0 A G|≤ e)
    (h1 : |P.utility 1 b 0 A G-Q.utility 1 b 0 A G|≤ e) :
    |P.success-Q.success|≤2*e := by
  have heq : P.success-Q.success=
      (P.utility 1 b 0 A G-Q.utility 1 b 0 A G)-
      (P.utility 0 b 0 A G-Q.utility 0 b 0 A G) := by
    rw [←utility_one_sub_zero P b A G,←utility_one_sub_zero Q b A G]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

def countTestErrorConstant (eta L : ℝ) : ℝ := 2+(1/L+2)/eta

theorem count_mass_error_of_two_payoff_tests (P Q : CountLaw 2)
    (eta L b e : ℝ) (heta : 0< eta) (he1 : eta≤1) (hL : 0< L) (hb : L≤ b) (he : 0≤ e)
    (h0 : |P.utility 0 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)-
      Q.utility 0 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)|≤ e)
    (h1 : |P.utility 1 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)-
      Q.utility 1 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)|≤ e) :
    ∀ r,|P.mass r-Q.mass r|≤ countTestErrorConstant eta L*e := by
  have hb0 : 0< b := hL.trans_le hb
  have hS := success_error_of_two_payoff_tests P Q b e
    (Schedule.affine 2 eta heta.le he1) (Schedule.once 2) h0 h1
  let u0 := P.utility 0 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)-
    Q.utility 0 b 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)
  have hDformula : P.duplicates-Q.duplicates=-(u0/b+(P.success-Q.success))/eta := by
    dsimp only [u0]
    rw [utility_zero_affine,utility_zero_affine]
    field_simp [hb0.ne',heta.ne']
    ring
  have hD : |P.duplicates-Q.duplicates|≤((1/L+2)/eta)*e := by
    rw [hDformula,abs_div,abs_neg,abs_of_pos heta]
    apply (div_le_div_of_nonneg_right (abs_add_le _ _) heta.le).trans
    rw [abs_div,abs_of_pos hb0]
    have hquot : |u0|/b≤ e/L :=
      (div_le_div_of_nonneg_right h0 hb0.le).trans
        (div_le_div_of_nonneg_left he hL hb)
    calc
      (|u0|/b+|P.success-Q.success|)/eta≤(e/L+2*e)/eta :=
        div_le_div_of_nonneg_right (add_le_add hquot hS) heta.le
      _=((1/L+2)/eta)*e := by ring
  have hC0 : 0≤((1/L+2)/eta)*e := by positivity
  have h2e : 0≤2*e := by positivity
  intro r
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [show r = 0 from Fin.ext hr, two_count_zero_mass,two_count_zero_mass]
    have heq : (1-P.success)-(1-Q.success)=-(P.success-Q.success) := by ring
    rw [heq,abs_neg]
    unfold countTestErrorConstant
    nlinarith
  · rw [show r = 1 from Fin.ext hr, two_count_one_mass,two_count_one_mass]
    have heq : (P.success-P.duplicates)-(Q.success-Q.duplicates)=
        (P.success-Q.success)-(P.duplicates-Q.duplicates) := by ring
    rw [heq]
    apply (abs_sub _ _).trans
    unfold countTestErrorConstant
    nlinarith
  · rw [show r = 2 from Fin.ext hr, ←two_count_duplicate_mass,←two_count_duplicate_mass]
    unfold countTestErrorConstant
    nlinarith

theorem native_count_mass_error_of_two_payoff_tests {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (i : Fin m)
    (eta L e : ℝ) (heta : 0< eta) (he1 : eta≤1) (hL : 0< L) (he : 0≤ e)
    (hA : G.A=Schedule.affine 2 eta heta.le he1) (hg : G.g=0)
    (a : JointAction 2) (hb : L≤ a.bid) (Q : CountLaw 2)
    (h0 : |(problem G i).payoff 0 a-
      Q.utility 0 a.bid 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)|≤ e)
    (h1 : |(problem G i).payoff 1 a-
      Q.utility 1 a.bid 0 (Schedule.affine 2 eta heta.le he1) (Schedule.once 2)|≤ e) :
    ∀ r,|((problem G i).outcome a).mass r-Q.mass r|≤ countTestErrorConstant eta L*e := by
  apply count_mass_error_of_two_payoff_tests ((problem G i).outcome a) Q
    eta L a.bid e heta he1 hL hb he
  · convert! h0 using 1
    change |((problem G i).outcome a).utility 0 a.bid 0 _ _-_|
      =|((problem G i).outcome a).utility 0 a.bid G.g G.A G.G-_|
    rw [hg,hA]
    simp only [CountLaw.utility_eq, zero_mul, sub_zero]
  · convert! h1 using 1
    change |((problem G i).outcome a).utility 1 a.bid 0 _ _-_|
      =|((problem G i).outcome a).utility 1 a.bid G.g G.A G.G-_|
    rw [hg,hA]
    simp only [CountLaw.utility_eq, zero_mul, sub_zero]

end FCAppendix.Affine.Hybrid.Native02
