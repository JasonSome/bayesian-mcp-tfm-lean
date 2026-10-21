import FCAppendix.Affine.Hybrid.TypicalCountApproximation

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical

lemma count_region_integer_tests {ξ L U : ℝ} (M A small ell gap : ℕ) (hM : 0 < M)
    (hg : NormalizedGuardRegion ξ L U (finiteCountPoint M A small ell gap)) :
    ell<small ∧ 2*ell+gap<A := by
  have hm : (0:ℝ)<M:=Nat.cast_pos.mpr hM
  have hD : normalizedMixed (finiteCountPoint M A small ell gap)=
      ((A:ℝ)-2*ell-gap)/(M:ℝ):=by dsimp [normalizedMixed,finiteCountPoint];ring
  have hR : normalizedResidual (finiteCountPoint M A small ell gap)=
      ((small:ℝ)-ell)/(M:ℝ):=by dsimp [normalizedResidual,finiteCountPoint];ring
  have hd:=(div_pos_iff_of_pos_right hm).mp (hD ▸ hg.1)
  have hr:=(div_pos_iff_of_pos_right hm).mp (hR ▸ hg.2.1)
  constructor
  · exact_mod_cast (show (ell:ℝ)<small by linarith)
  · exact_mod_cast (show ((2*ell+gap:ℕ):ℝ)<A by push_cast;linarith)

theorem eventually_typical_counts_guarded (a h ρ z ξ L U : ℝ)
    (ha : 0 < a) (hz0 : 0  ≤  z) (hz1 : z<1) (hξ : 0 < ξ) (hξ1 : ξ<1) (hL : 0 < L)
    (hlower : h/2<ρ) (hupper : ρ<a+h/2)
    (hq0 : 0<sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z<1)
    (hboxlo : (1-ξ)*U<(1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U<L)
    (c : ℕ→ℕ) (hc : Tendsto (fun M=>(c M:ℝ)/(M:ℝ)) atTop (𝓝 ρ)) :
    ∃δ : ℝ,0 < δ ∧ ∀ᶠM : ℕ in atTop,∀A H₀ H₁ : ℕ,
      |(A:ℝ)-(M:ℝ)*a|  ≤  M*δ→
      |(H₀:ℝ)-(M:ℝ)*(h/2)|  ≤  M*δ→
      |(H₁:ℝ)-(M:ℝ)*(h/2)|  ≤  M*δ→
      let d₀:=activeResidual (c M) A H₀
      let d₁:=activeResidual (c M) A H₁
      let ell:=exclusiveQuota z A
      let gap:=residualDifference d₀ d₁
      ell < min d₀ d₁ ∧ 2*ell+gap<A ∧
      (d₀≠d₁→1  ≤  2*ell+gap ∧ 2  ≤  A) ∧
      ∀(ι : Type) [Fintype ι] [DecidableEq ι],Fintype.card ι=A→
        ∀(b : ι→ℝ),(∀i,b i∈Icc L U)→
        ∀E₁ E₂ : Finset ι,Disjoint E₁ E₂→E₁.card=ell+gap→E₂.card=ell→
          ∃Q : GuardedData ι,Q.xi=ξ ∧ Q.bid=b ∧ Q.owner₁=E₁ ∧ Q.owner₂=E₂ ∧
            Q.residual=min d₀ d₁-ell ∧ Q.owner₁.card+Q.residual=max d₀ d₁ ∧
            Q.owner₂.card+Q.residual=min d₀ d₁ := by
  obtain ⟨η,hη,hregion⟩:=exists_normalized_guard_neighborhood a h ρ z ξ L U
    ha hz1 hξ hξ1 hq0 hq1 hboxlo hboxhi
  let δ:=min (η/16) (min ((ρ-h/2)/4) ((a+h/2-ρ)/6))
  have hδ : 0 < δ:=lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hδη : δ  ≤  η/16:=min_le_left _ _
  have hδlo : δ  ≤  (ρ-h/2)/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hδhi : δ  ≤  (a+h/2-ρ)/6:=(min_le_right _ _).trans (min_le_right _ _)
  have hδlower : 2*δ<ρ-h/2:=by linarith
  have hδupper : 3*δ<a+h/2-ρ:=by linarith
  have hcapClose : ∀ᶠM : ℕ in atTop,|(c M:ℝ)/(M:ℝ)-ρ|<δ:=by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hc) δ hδ
  have hroundClose : ∀ᶠM : ℕ in atTop,1/(M:ℝ)<η/4:=
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually (Iio_mem_nhds (by positivity))
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcapClose,hroundClose,eventually_gt_atTop (0:ℕ)] with M hcapM hroundM hM
  intro A H₀ H₁ hA hH₀ hH₁
  have hm : (0:ℝ)<M:=Nat.cast_pos.mpr hM
  have hcap : |(c M:ℝ)-(M:ℝ)*ρ|  ≤  M*δ := by
    have he : (c M:ℝ)/(M:ℝ)-ρ=((c M:ℝ)-(M:ℝ)*ρ)/(M:ℝ):=by field_simp
    rw [he,abs_div,abs_of_pos hm] at hcapM
    have hh:=(div_lt_iff₀ hm).mp hcapM
    nlinarith
  let d₀:=activeResidual (c M) A H₀
  let d₁:=activeResidual (c M) A H₁
  let ell:=exclusiveQuota z A
  let gap:=residualDifference d₀ d₁
  let p:=finiteCountPoint M A (min d₀ d₁) ell gap
  have herrors:=typical_count_point_errors hM hδ.le hz0 hz1.le hcap hA hH₀ hH₁ hδlower hδupper
  have hp : NormalizedGuardRegion ξ L U p := by
    apply hregion
    intro i
    fin_cases i
    · exact herrors.1.trans_lt (by linarith)
    · exact herrors.2.1.trans_lt (by linarith)
    · exact herrors.2.2.1.trans_lt (by linarith)
    · exact herrors.2.2.2.trans_lt (by linarith)
  obtain ⟨hsmall,hD⟩:=count_region_integer_tests M A (min d₀ d₁) ell gap hM hp
  refine ⟨hsmall,hD,?_,?_⟩
  · intro hne
    dsimp only [gap,residualDifference] at hD ⊢
    omega
  · intro ι _ _ hcard b hb E₁ E₂ hdis hE₁ hE₂
    exact exists_guardedData_of_count_region hξ hξ1 hL M A (min d₀ d₁) (max d₀ d₁) ell
      hM hcard (show min d₀ d₁ ≤ max d₀ d₁ from min_le_max) hp b hb E₁ E₂ hdis hE₁ hE₂

end FCAppendix.Affine.Hybrid
