import FCAppendix.Probability.CountLaw

namespace FCAppendix.CountLaw
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

theorem test_limit_of_mass_limits {n q : ℕ} (hq : q ≤ n)
    (μ : ℕ → CountLaw n) (s : ℕ → ℝ) (hsp : ∀ᶠ t in atTop, 0 < s t)
    (hs : Tendsto s atTop (𝓝 0)) (a : Fin (n+1) → ℝ)
    (hmass : ∀ j : Fin (n+1), q ≤ j.val →
      Tendsto (fun t => (μ t).prob (fun r => r.val=j.val)/(s t)^j.val) atTop (𝓝 (a j)))
    (f : Fin (n+1) → ℝ) (hf : ∀ j, j.val<q → f j=0) :
    Tendsto (fun t => (μ t).expect f/(s t)^q) atTop
      (𝓝 (a ⟨q,by omega⟩*f ⟨q,by omega⟩)) := by
  classical
  have hp t (j : Fin (n+1)) : (μ t).prob (fun r => r.val=j.val)=(μ t).mass j := by
    have hv (r : Fin (n+1)) : r.val=j.val ↔ r=j := Fin.val_inj
    simp [FiniteLaw.prob,FiniteLaw.expect,hv]
  have hterm (j : Fin (n+1)) :
      Tendsto (fun t => (μ t).mass j*f j/(s t)^q) atTop
        (𝓝 (if j.val=q then a j*f j else 0)) := by
    by_cases hj : j.val<q
    · simp only [hf j hj,mul_zero,zero_div,if_neg (ne_of_lt hj)]
      exact tendsto_const_nhds
    have hjq : q ≤ j.val := le_of_not_gt hj
    have hh := hmass j hjq
    simp_rw [hp] at hh
    have he t (ht : 0 < s t) : (μ t).mass j*f j/(s t)^q =
        ((μ t).mass j/(s t)^j.val)*(s t)^(j.val-q)*f j := by
      have hpow : (s t)^j.val=(s t)^q*(s t)^(j.val-q) := by
        rw [← pow_add,show q+(j.val-q)=j.val by omega]
      rw [hpow]
      field_simp
    by_cases heq : j.val=q
    · simp only [heq,Nat.sub_self,pow_zero,mul_one] at he
      simp only [if_pos heq]
      rw [heq] at hh
      exact (hh.mul_const (f j)).congr' (hsp.mono fun t ht => (he t ht).symm)
    · simp only [if_neg heq]
      have hh' := (hh.mul (hs.pow (j.val-q))).mul_const (f j)
      simp only [zero_pow (show j.val-q ≠ 0 by omega),mul_zero,zero_mul] at hh'
      exact hh'.congr' (hsp.mono fun t ht => (he t ht).symm)
  have hh := tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  have he : (∑ j : Fin (n+1), if j.val=q then a j*f j else 0) = a ⟨q,by omega⟩*f ⟨q,by omega⟩ := by
    have hiff (j : Fin (n+1)) : j.val=q ↔ j=(⟨q,Nat.lt_succ_of_le hq⟩ : Fin (n+1)) := by
      constructor
      · intro h; apply Fin.ext; exact h
      · intro h; exact congrArg Fin.val h
    simp only [hiff,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [he] at hh
  simpa only [FiniteLaw.expect,Finset.sum_div] using hh

theorem conditional_copies_limit_of_mass_limits {n : ℕ} (hn : 2 ≤ n)
    (μ : ℕ → CountLaw n) (s : ℕ → ℝ) (hsp : ∀ᶠ t in atTop, 0 < s t)
    (hs : Tendsto s atTop (𝓝 0)) (a : Fin (n+1) → ℝ)
    (hmass : ∀ j : Fin (n+1), 2 ≤ j.val →
      Tendsto (fun t => (μ t).prob (fun r => r.val=j.val)/(s t)^j.val) atTop (𝓝 (a j)))
    {c : ℝ} (hc : 0 < c) (hS : Tendsto (fun t => (μ t).success/s t) atTop (𝓝 c)) :
    Tendsto (fun t => (μ t).duplicates/(s t)^2) atTop (𝓝 (a ⟨2,by omega⟩)) ∧
    Tendsto (fun t => (μ t).prob (fun r => 2 ≤ r.val)/(s t)^2) atTop (𝓝 (a ⟨2,by omega⟩)) ∧
    Tendsto (fun t => ((μ t).load/(μ t).success-1)/s t) atTop (𝓝 (a ⟨2,by omega⟩/c)) ∧
    Tendsto (fun t => ((μ t).prob (fun r => 2 ≤ r.val)/(μ t).success)/s t)
      atTop (𝓝 (a ⟨2,by omega⟩/c)) := by
  classical
  have hd : Tendsto (fun t => (μ t).duplicates/(s t)^2) atTop (𝓝 (a ⟨2,by omega⟩)) := by
    have hh := test_limit_of_mass_limits hn μ s hsp hs a hmass
      (fun j => (j.val:ℝ)-successIndicator j.val) (by
        intro j hj
        rcases (show j.val=0 ∨ j.val=1 by omega) with h0 | h1
        · simp [successIndicator,h0]
        · simp [successIndicator,h1])
    have he : (a ⟨2,by omega⟩*((2:ℝ)-successIndicator 2))=a ⟨2,by omega⟩ := by
      norm_num [successIndicator]
    simp only [Nat.cast_ofNat] at hh
    rw [he] at hh
    simpa only [← duplicates_eq_expect] using hh
  have hP : Tendsto (fun t => (μ t).prob (fun r => 2 ≤ r.val)/(s t)^2) atTop (𝓝 (a ⟨2,by omega⟩)) := by
    have hh := test_limit_of_mass_limits hn μ s hsp hs a hmass
      (fun j => if 2 ≤ j.val then (1:ℝ) else 0) (by
        intro j hj
        simp only [if_neg (not_le.mpr hj)])
    simpa only [FiniteLaw.prob_eq_expect,le_refl,if_true,mul_one] using hh
  have hsuccess : ∀ᶠ t in atTop, 0 < (μ t).success := by
    filter_upwards [hsp,hS.eventually_const_lt hc] with t ht hSt
    exact (div_pos_iff.mp hSt).elim (fun h => h.1) (fun h => (not_lt_of_ge ht.le h.2).elim)
  refine ⟨hd,hP,?_,?_⟩
  · apply (hd.div hS hc.ne').congr'
    filter_upwards [hsp,hsuccess] with t ht hSt
    simp only [Pi.div_apply]
    unfold duplicates
    field_simp
  · apply (hP.div hS hc.ne').congr'
    filter_upwards [hsp,hsuccess] with t ht hSt
    simp only [Pi.div_apply]
    field_simp

end FCAppendix.CountLaw
