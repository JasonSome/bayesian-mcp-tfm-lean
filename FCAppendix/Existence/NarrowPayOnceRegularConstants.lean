import FCAppendix.Existence.NarrowPayOnceExpectedBounds

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList

theorem exists_uniform_curvature_upper {n : ℕ} (hn : 2≤n) {w lo hi : ℝ}
    (hw : 0<w) (hlo : 0<lo) (hhi : hi<1) :
    ∃M : ℝ, 0<M ∧ ∀R c : ℕ, 1≤c → c≤R → density R c∈Icc lo hi →
      referenceCurvature n R (density R c) w (referenceBid n R c w)≤M := by
  let s := Icc lo hi×ˢIcc (0:ℝ) 1
  have hs : IsCompact s := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn (fun x : ℝ×ℝ=>thetaCurvature n w x.1 x.2) s := by
    intro x hx
    exact (continuousAt_thetaCurvature hn hw x
      ⟨⟨hlo.trans_le hx.1.1,hx.1.2.trans_lt hhi⟩,hx.2.1⟩).continuousWithinAt
  obtain ⟨M,hM⟩ := hs.bddAbove_image hf
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro R c hc hcR hrho
  have hR : 0<R := by omega
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hRone : (1:ℝ)≤R := by exact_mod_cast (show 1≤R by omega)
  have htheta : 1/(R:ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(one_div_pos.mpr hRreal).le,(div_le_one hRreal).mpr hRone⟩
  have hh := (hM ⟨(density R c,1/(R:ℝ)),⟨hrho,htheta⟩,rfl⟩).trans (le_max_left M 1)
  simpa only [thetaCurvature_eq_referenceCurvature hn hRreal
    ⟨hlo.trans_le hrho.1,hrho.2.trans_lt hhi⟩] using hh

theorem exists_uniform_small_finiteScoreControl {n : ℕ} (hn : 2≤n) {w0 lo hi : ℝ}
    (hw0 : 0<w0) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1)
    (r : ℝ→ℝ) (hr : ∀kappa,0<kappa → 0<r kappa) :
    ∃kappa eps deltaStar : ℝ, 0<kappa ∧ 0<eps ∧ 0<deltaStar ∧ deltaStar≤w0/2 ∧ eps≤r kappa ∧
      ∀R c : ℕ, 1≤c → c≤R → density R c∈Icc lo hi →
      ∀delta∈Icc (0:ℝ) deltaStar, FiniteScoreControl n R c w0 kappa eps delta := by
  obtain ⟨kappa,eps0,delta0,hk,he,hd,hek,he1,hdw,hall⟩ :=
    exists_uniform_score_neighborhood hn hw0 hlo hlohi hhi
  let eps := min eps0 (r kappa)
  let T := (n:ℝ)*firstJetBound n (kappa/2)
  let deltaStar := min delta0 (kappa*eps/(16*(T+1)))
  have heps : 0<eps := lt_min he (hr kappa hk)
  have heps0 : eps≤eps0 := min_le_left _ _
  have hT : 0≤T := by dsimp [T,firstJetBound]; positivity
  have hds : 0<deltaStar := lt_min hd (by positivity)
  have hds0 : deltaStar≤delta0 := min_le_left _ _
  have hsmall : T*deltaStar≤kappa*eps/16 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(T+1))).mp
      (min_le_right delta0 (kappa*eps/(16*(T+1))))
    change deltaStar*(16*(T+1))≤kappa*eps at hh
    nlinarith
  refine ⟨kappa,eps,deltaStar,hk,heps,hds,hds0.trans hdw,min_le_right _ _,?_⟩
  intro R c hc hcR hrho delta hdelta
  obtain ⟨hB,hBw,hA,hgap,hint,hderiv⟩ := hall R c hc hcR hrho
  refine ⟨hn,hc,hcR,hw0,hk,heps,hdelta.1,hB,heps0.trans hek,hA,hgap,?_,?_,?_⟩
  · intro b hb
    apply hint b
    intro i
    exact (abs_le.mpr ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩).trans heps0
  · intro w hw b hb
    apply hderiv w (hw.trans (hdelta.2.trans hds0)) b
    intro i
    exact (abs_le.mpr ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩).trans heps0
  · have hh := (mul_le_mul_of_nonneg_left hdelta.2 hT).trans hsmall
    change T*delta≤kappa*eps/4
    nlinarith [mul_pos hk heps]

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)

theorem marginal_upper {hi : ℝ} (hhi : hi<1) (hrho : density R c≤hi)
    (heps : eps≤(1-hi)*kappa/(16*(n:ℝ)))
    (b : Fin (R+1)→ℝ) (hb : b∈bidBox (U.B-eps) (U.B+eps)) (i : Fin (R+1)) :
    kernelMarginal n c b i≤(1+hi)/2 := by
  have hRreal : (0:ℝ)<R := by exact_mod_cast (show 0<R by have:=U.c_pos; have:=U.c_le; omega)
  have hcreal : (1:ℝ)≤c := by exact_mod_cast U.c_pos
  have hcRreal : (c:ℝ)≤R := by exact_mod_cast U.c_le
  have hrho0 := density_bounds hRreal hcreal hcRreal
  have hcap : (((R+1:ℕ):ℝ))*density R c=c := by
    simp only [Nat.cast_add,Nat.cast_one]
    unfold density
    field_simp
  have hbound := kernelMarginal_uniform_difference U.n_ge (by simpa using (show c≤R+1 by have:=U.c_le; omega))
    hrho0 U.eps_pos.le U.eps_lt_bid (ι:=Fin (R+1)) (by simpa using hcap) b
    (fun i=>abs_le.mpr ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩) i
  have hn : (0:ℝ)<n := by exact_mod_cast (show 0<n by have:=U.n_ge; omega)
  have hsmall := (le_div_iff₀ (by positivity : (0:ℝ)<16*(n:ℝ))).mp heps
  have hratio : 2*(n:ℝ)*eps/(U.B-eps)≤(1-hi)/2 := by
    apply (div_le_iff₀ U.lower_pos).mpr
    have hfloor := mul_le_mul_of_nonneg_left U.lower_floor (sub_nonneg.mpr hhi.le)
    nlinarith [mul_pos U.kappa_pos (sub_pos.mpr hhi)]
  have hh := (abs_le.mp (hbound.trans hratio)).2
  linarith

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
