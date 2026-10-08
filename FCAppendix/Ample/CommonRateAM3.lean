import FCAppendix.Ample.CommonRateSelections
import FCAppendix.Ample.SlackEndpoint

noncomputable section
namespace FCAppendix.Ample
open Finset Filter Topology Set Real
open scoped BigOperators

theorem commonRate_singleton_rate_eq {n : ℕ} (hn : 0<n) {rho p : ℝ}
    (hrho : 0<rho) (hrho1 : rho<1) (hp : 0<p) (hpr : p/n<rho) :
    rivalRate n rho 1 (singletonOnly p)=binaryKL rho (p/n) := by
  have he : (fun j => if j≤1 then singletonOnly p j else 0)=singletonOnly p := by
    funext j
    by_cases hj : j=1 <;> simp [singletonOnly,hj]
  have hh := prefixRate_eq_rivalRate (show 1≤n by omega) rho (singletonOnly p)
  rw [he] at hh
  rw [← hh]
  simpa [singletonOnly] using prefixRate_one_eq_binaryKL («π» := singletonOnly p)
    (show 1≤n by omega) hrho hrho1 (by simpa [singletonOnly] using hp)
    (by simpa [singletonOnly] using hpr)

theorem commonRate_partial_open {n k r : ℕ} {rho : ℝ}
    (hk : 0<k) (hkn : k<n) (hrho : 0<rho) (hrho1 : rho<1)
    (hr : (n:ℝ)*rho≤r) : (k:ℝ)*rho < (min k r : ℕ) := by
  by_cases hkr : k≤r
  · rw [min_eq_left hkr]
    have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
    nlinarith
  · rw [min_eq_right (le_of_not_ge hkr)]
    have hknR : (k:ℝ)<n := Nat.cast_lt.mpr hkn
    have hh := mul_lt_mul_of_pos_right hknR hrho
    exact hh.trans_le hr

theorem commonRate_largest_positive {n : ℕ} {pi : ℕ → ℝ}
    (hn : 0<n) (hpi : ∀ j ∈ Finset.Icc 1 n, 0≤pi j) (hp1 : 0<pi 1) :
    ∃ r ∈ Finset.Icc 1 n, 0<pi r ∧ ∀ j ∈ Finset.Icc (r+1) n, pi j=0 := by
  revert hn hpi hp1
  induction n with
  | zero =>
    intro hn _ _
    omega
  | succ n ih =>
    intro _ hpi hp1
    by_cases hlast : 0 < pi (n+1)
    · refine ⟨n+1, Finset.mem_Icc.mpr ⟨Nat.succ_pos n, le_rfl⟩, hlast, ?_⟩
      intro j hj
      have hb := Finset.mem_Icc.mp hj
      omega
    · have hn : 0 < n := by
        by_contra hnot
        have he : n=0 := by omega
        subst n
        exact hlast hp1
      have hpi' : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j := by
        intro j hj
        exact hpi j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, by
          have := (Finset.mem_Icc.mp hj).2
          omega⟩)
      obtain ⟨r, hr, hpr, htop⟩ := ih hn hpi' hp1
      have hnzero : pi (n+1)=0 := le_antisymm (le_of_not_gt hlast)
        (hpi (n+1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos n, le_rfl⟩))
      refine ⟨r, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by
        have := (Finset.mem_Icc.mp hr).2
        omega⟩, hpr, ?_⟩
      intro j hj
      by_cases he : j=n+1
      · simpa only [he] using hnzero
      · exact htop j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, by
          have := (Finset.mem_Icc.mp hj).2
          omega⟩)

end FCAppendix.Ample

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Topology Set Real
open Ample
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem commonRate_AM3_lower (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0<n) (hc : 0<c) (hcm : c ≤ m-1)
    (hA : Γ.A=Schedule.ppi n) (hf : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) :
    congestProb n (m-1) c 1 (singletonOnly (positiveRouteMass Γ (fun k => k=1))) ≤
      actualAllFailure Γ := by
  rw [congest_one_eq_binomial hn (by omega)
    (singletonOnly_valid hn (positiveRouteMass_nonneg Γ _) (positiveRouteMass_le_one Γ _)),
    singletonOnly_marginal hn]
  simpa only [actualAllFailure,dif_pos hm] using
    ppi_AM3_positive Γ hm hn hc hA hf hatom hj hu hact ⟨0,hm⟩

theorem commonRate_singleton_event_rate {M C : ℕ → ℕ} {pseq : ℕ → ℝ}
    {p rho : ℝ} (hn : 0<n) (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (h01 : ∀ t, 0≤pseq t ∧ pseq t≤1)
    (hconv : Tendsto pseq atTop (𝓝 p))
    (hp : 0<p) (hrho : 0<rho) (hrho1 : rho<1) (hpr : p/n<rho) :
    HasPopulationRate M
      (fun t => congestProb n (M t-1) (C t) 1 (singletonOnly (pseq t)))
      (binaryKL rho (p/n)) := by
  have hp1 : p≤1 := le_of_tendsto hconv (Eventually.of_forall fun t => (h01 t).2)
  have hlam := singletonOnly_valid hn hp.le hp1
  have hs : contactMarginal n (singletonOnly p)<rho := by
    rw [singletonOnly_marginal hn]
    exact hpr
  have ht : ∃ j ∈ Finset.Icc 1 n, 0<singletonOnly p j ∧
      ((1:ℕ):ℝ)*rho<(min 1 j:ℕ) := by
    refine ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hn⟩,by simpa [singletonOnly] using hp,?_⟩
    simpa using hrho1
  have hh := ample_event_rate (by omega : 1≤1) (show 1≤n by omega)
    (fun t => singletonOnly_valid hn (h01 t).1 (h01 t).2) hlam (by
      intro j _
      by_cases hj : j=1
      · simpa [singletonOnly,hj] using hconv
      · simpa only [singletonOnly,if_neg hj] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
    hM hC hs ht
  rw [commonRate_singleton_rate_eq hn hrho hrho1 hp hpr] at hh
  exact hh

end FCAppendix.Bayes
