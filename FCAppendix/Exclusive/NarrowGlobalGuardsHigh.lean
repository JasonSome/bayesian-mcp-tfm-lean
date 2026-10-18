import FCAppendix.Exclusive.NarrowGlobalGuardsExpectedTails

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory

lemma pricedPayoff_zero_bid (n k : ℕ) (a : UserTariff) (lam : ℝ) (hlam : 0 < lam) :
    pricedPayoff n k a 0 lam=0 := by
  have hp : menuMarginal n 0 lam=0 := by
    simp [menuMarginal,max_eq_right hlam.le,demand,div_self hlam.ne']
  simp [pricedPayoff,hp,PayOnce.success]

lemma normalizedPrice_unique (d : ℕ) (p0 : ℝ) :
    normalizedPrice d .unique p0=(1-p0)^d := by
  simp [normalizedPrice,fTariff,fUnique]

lemma exists_uniform_reference_utility_margin (d : ℕ) (hd : 1 ≤ d)
    (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ a : UserTariff, a.Allowed →
      gamma ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  obtain ⟨gamma,hgamma,hgap⟩ := referenceRawGap_uniform_compact d 1 hd
    (by omega) (by omega) p0 0 hp0 hp1 le_rfl
  refine ⟨gamma,hgamma,?_⟩
  intro a ha
  have hlam : 0 < normalizedPrice d a p0 := one_div_pos.mpr
    (fTariff_pos_and_derivative_pos d hd a ha hp0.le hp1).1
  have h := hgap a ha 0 ⟨le_refl _,le_refl _⟩
  simpa only [referenceRawGap,pricedPayoff_zero_bid _ _ _ _ hlam,sub_zero] using h

theorem exists_uniform_high_global_guard (d : ℕ) (hd : 1 ≤ d)
    (p0 radius lower upper : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hradius : 0 < radius) (hlower : 0 < lower)
    (hprices : ∀ a : UserTariff, a.Allowed → normalizedPrice d a p0 ∈ Icc lower upper) :
    ∃ gap priceTolerance valueTolerance badTolerance bidCutoff : ℝ,
      0 < gap ∧ 0 < priceTolerance ∧ 0 < valueTolerance ∧ 0 < badTolerance ∧ 0 < bidCutoff ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
        (E : Set Ω), MeasurableSet E → ∀ a : UserTariff, a.Allowed →
        ∀ G : Schedule (d+1), ∀ g v : ℝ, 0 ≤ g → 0 ≤ v → v ≤ 2 →
        |v-1|+g*(d+1:ℕ) ≤ valueTolerance → ∀ k : ℕ, k ≤ d+1 →
        ∀ b : ℝ, 0 ≤ b → (k=d+1 → radius ≤ |b-referenceCentralBid d a p0|) →
        ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
        (∀ w ∈ E, lam w ∈ Icc lower upper ∧
          |lam w-normalizedPrice d a p0| < priceTolerance) → mu.real Eᶜ ≤ badTolerance →
        (∫ w, LowType.binomialPayoff a G k g v b (activeDemand (d+1) b (lam w)) ∂mu)+gap ≤
          referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  let n := d+1
  let lu := normalizedPrice d .unique p0
  let M : ℝ := (d:ℝ)*lu*(1-p0)
  have hlu : 0 < lu := by dsimp [lu]; rw [normalizedPrice_unique]; positivity
  have hM : 0 < M := mul_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hlu) (sub_pos.mpr hp1)
  have hu : 0 < upper := hlower.trans_le ((hprices .unique trivial).1.trans (hprices .unique trivial).2)
  let error := min (1/2) (min (lu/2) (M/(4*((n:ℝ)+1))))
  have he0 : 0 < error := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have helu : error ≤ lu/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hebudget : ((n:ℝ)+1)*error ≤ M/4 := by
    have he := (le_div_iff₀ (show (0:ℝ)<4*((n:ℝ)+1) by positivity)).mp
      (show error ≤ M/(4*((n:ℝ)+1)) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith only [he]
  let cap := M/(4*(n:ℝ)*upper)
  have hcap : 0 < cap := by dsimp [cap,n]; positivity
  obtain ⟨failure,B,hf0,hfcap,hfhalf,hB,hfsmall,hcut⟩ :=
    exists_small_failure_bid_cutoff n lower upper 2 cap hlower ((hprices .unique trivial).1.trans (hprices .unique trivial).2) (by norm_num) hcap
  have hf1 : failure < 1 := by linarith only [hfhalf]
  have hfBudget : (n:ℝ)*upper*failure ≤ M/4 := by
    have hh := (le_div_iff₀ (show (0:ℝ)<4*(n:ℝ)*upper by dsimp [n]; positivity)).mp hfcap
    nlinarith only [hh]
  obtain ⟨gu,hgu,hguBound⟩ := exists_uniform_reference_utility_margin d hd p0 hp0 hp1
  obtain ⟨gl,dl,vl,bl,hgl,hdl,hvl,hbl,hl⟩ := finite_all_lower_routes_compact_guard d hd
    p0 B lower upper hp0 hp1 hB.le hlower hprices
  obtain ⟨gf,df,vf,bf,hgf,hdf,hvf,hbf,hf⟩ := finite_full_route_compact_guard d hd
    p0 B radius lower upper hp0 hp1 hradius hB.le hlower hprices
  let gap := min gu (min gl (min gf (M/4)))
  let priceTolerance := min dl (min df error)
  let valueTolerance := min vl (min vf error)
  let uniqueBad := M/(4*(2+M/2))
  let badTolerance := min bl (min bf (min uniqueBad (1/4)))
  have hgap : 0 < gap := lt_min hgu (lt_min hgl (lt_min hgf (by positivity)))
  have hpt : 0 < priceTolerance := lt_min hdl (lt_min hdf he0)
  have hvt : 0 < valueTolerance := lt_min hvl (lt_min hvf he0)
  have hbt : 0 < badTolerance := lt_min hbl (lt_min hbf (lt_min (by dsimp [uniqueBad]; positivity) (by norm_num)))
  refine ⟨gap,priceTolerance,valueTolerance,badTolerance,B,hgap,hpt,hvt,hbt,hB,?_⟩
  intro Ω _ mu _ E hE a ha G g v hg hv0 hv2 hvalue k hkn b hb houtside lam hlam hlam0 hgood hbad
  have hgapU : gap ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0 :=
    (min_le_left _ _).trans (hguBound a ha)
  by_cases hk0 : k=0
  · subst k
    simpa [LowType.binomialPayoff,PayOnce.success,binomialPolynomial,G.zero] using hgapU
  have hk : 1 ≤ k := by omega
  by_cases hbB : b ≤ B
  · have hbid : b ∈ Icc (0:ℝ) B := ⟨hb,hbB⟩
    by_cases hfull : k=d+1
    · subst k
      have h := hf mu E hE a ha G g v hg hv2
        (hvalue.trans ((min_le_right _ _).trans (min_le_left _ _))) b hbid (houtside rfl)
        lam hlam hlam0 (fun w hw => ⟨(hgood w hw).1,((hgood w hw).2).trans_le
          ((min_le_right _ _).trans (min_le_left _ _))⟩)
        (hbad.trans ((min_le_right _ _).trans (min_le_left _ _)))
      have hm : gap ≤ gf := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      linarith only [h,hm]
    · have h := hl k hk (by omega) mu E hE a ha G g v hg hv2
        (hvalue.trans (min_le_left _ _)) b hbid lam hlam hlam0
        (fun w hw => ⟨(hgood w hw).1,((hgood w hw).2).trans_le (min_le_left _ _)⟩)
        (hbad.trans (min_le_left _ _))
      have hm : gap ≤ gl := (min_le_right _ _).trans (min_le_left _ _)
      linarith only [h,hm]
  · have hbTail := hcut b (le_of_not_ge hbB)
    have hbadQuarter : mu.real Eᶜ ≤ 1/4 := hbad.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hbadNeg : mu.real Eᶜ < 1/(2+1) := lt_of_le_of_lt hbadQuarter (by norm_num)
    have hgoodPrice : ∀ w ∈ E, lam w ∈ Icc lower upper := fun w hw => (hgood w hw).1
    have hzero (hneg : (∫ w, LowType.binomialPayoff a G k g v b (demand n b (lam w)) ∂mu)<0) :
        (∫ w, LowType.binomialPayoff a G k g v b (activeDemand (d+1) b (lam w)) ∂mu)+gap ≤
          referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
      simp only [activeDemand,if_pos hbTail.1]
      dsimp [n] at hneg
      linarith only [hneg.le,hgapU]
    by_cases hfull : k=d+1
    · subst k
      cases a with
      | affine eta =>
        apply hzero
        exact integral_affine_tail_negative mu E hE n n (by dsimp [n]; omega) hk le_rfl eta ha G
          g v b lower upper failure 2 hg hv0 hv2 (by norm_num) hlower hf0 hfhalf hfsmall
          hbTail.1 hbTail.2 lam hlam hlam0 hgoodPrice hbadNeg
      | unique =>
        have herror : |v-1|+g*(d+1:ℕ) ≤ error := hvalue.trans
          ((min_le_right _ _).trans (min_le_right _ _))
        have hve : v ≤ 1+error := by
          have hg0 := mul_nonneg hg (Nat.cast_nonneg (d+1))
          linarith only [herror,hg0,le_abs_self (v-1)]
        have hclose : ∀ w ∈ E, lam w ∈ Icc (lu-error) upper := by
          intro w hw
          have hc := (abs_lt.mp ((hgood w hw).2.trans_le
            ((min_le_right _ _).trans (min_le_right _ _)))).1
          exact ⟨by dsimp [lu]; linarith only [hc],(hgood w hw).1.2⟩
        have hlue : 0 < lu-error := by linarith only [hlu,helu]
        have h := integral_unique_tail_reference_gap mu E hE d hd G g v b (lu-error) upper failure lu p0 error
          hg hv0 hv2 hve hlue hf0 hf1 hbTail.1 (by simpa only [n,Nat.add_sub_cancel] using hbTail.2)
          hlu hp0 hp1 (by dsimp [lu]; rw [normalizedPrice_unique]) (le_refl _)
          (by dsimp [n] at hebudget hfBudget; push_cast at hebudget hfBudget ⊢; dsimp [M] at *; linarith only [hebudget,hfBudget])
          lam hlam hlam0 hclose
          (hbad.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
        have hm : gap ≤ M/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
        simp only [activeDemand,if_pos hbTail.1]
        change _+M/4 ≤ _ at h
        linarith only [h,hm]
    · apply hzero
      exact integral_lower_route_tail_negative mu E hE n k (by dsimp [n]; omega) hk (by dsimp [n]; omega)
        a ha G g v b lower upper failure 2 hg hv0 hv2 (by norm_num) hlower hf0 hfhalf hfsmall
        hbTail.1 hbTail.2 lam hlam hlam0 hgoodPrice hbadNeg

end FCAppendix.Exclusive.Narrow.Global
