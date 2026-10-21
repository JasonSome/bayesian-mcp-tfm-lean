import FCAppendix.Affine.Uniform06.EntryModerateRootFinite

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRelativeWeight
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open EntryRawTiltedFiber EntryUntilting EntryRawSignMoments EntryModerateProfile
open scoped BigOperators

lemma polynomial_fourthRoot_tail (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (j : ℕ) :
    Tendsto (fun m => (N m:ℝ)^j*Real.exp (-Real.sqrt (Real.sqrt (N m:ℝ)))) atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hN))
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((4*j:ℕ):ℝ) 1 (by norm_num)).comp hs
  apply hh.congr
  intro m
  dsimp only [Function.comp_def]
  rw [Real.rpow_natCast,show 4*j=2*(2*j) by omega,pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _),pow_mul,Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

lemma radius_times_N (N : ℕ) (hN : 0 < N) :
    radius N*(N:ℝ)=Real.sqrt (N:ℝ)*Real.sqrt (Real.sqrt (N:ℝ)) := by
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hR : 0 < Real.sqrt (Real.sqrt (N:ℝ)) := by positivity
  unfold radius
  field_simp [hR.ne']
  nlinarith [Real.sq_sqrt hNr.le,Real.sq_sqrt (Real.sqrt_nonneg (N:ℝ))]

lemma moderate_wide_tail (N : ℕ → ℕ) (hNp : ∀ m,0 < N m) (hN : Tendsto N atTop atTop)
    (θ : ℕ → ℝ)
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop) (j : ℕ) :
    Tendsto (fun m => (N m:ℝ)^j*Real.exp (-θ m*(radius (N m)*(N m:ℝ)))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ (polynomial_fourthRoot_tail N hN j)
  filter_upwards [hθN.eventually_ge_atTop 1] with m hm
  have hr := Real.sqrt_nonneg (Real.sqrt (N m:ℝ))
  have he := mul_le_mul_of_nonneg_right hm hr
  rw [one_mul] at he
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [radius_times_N (N m) (hNp m)]
  nlinarith

theorem exact_reverse_seed_integral (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {N C : ℕ} {b θ M : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ)
    (F : EntryIIDCentral.Row (Ω := RowRival) N → ℝ) (hF : Measurable F)
    (hM : ∀ x,|F x| ≤ M) :
    (∫ x,F x ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      Real.exp ((N:ℝ)*cgf (RawMixedSource.demand (xi i) b) (RawMixedSource.source i G) (-θ)+θ*C)*
        (∫ x,Real.exp (-θ*balanced i C b x.1)*F x
          ∂EntryIIDCentral.rowLaw (rawTilt i G b (-θ)) N) := by
  let ν := RawMixedSource.source i G
  let R := rawTilt i G b (-θ)
  letI := rawTilt_probability i G hb (-θ)
  have hFI : Integrable F (EntryIIDCentral.rowLaw ν N) :=
    Integrable.of_bound hF.aestronglyMeasurable M
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x)
  have hWlo (r : Fin N → RowRival) : -(N:ℝ) ≤ balanced i C b r := by
    have hs : iidSum (RawMixedSource.demand (xi i) b) N r ≤ N := by
      calc
        _ ≤ ∑ _j : Fin N,(1:ℝ) := Finset.sum_le_sum fun j _ =>
          (RawMixedSource.demand_bounds (xi_pos i) hb (r j)).2
        _ = _ := by simp
    dsimp [balanced]
    linarith [show (0:ℝ) ≤ C from Nat.cast_nonneg C]
  have hbound (x : EntryIIDCentral.Row (Ω := RowRival) N) :
      |Real.exp (-θ*balanced i C b x.1)*F x| ≤ Real.exp (θ*N)*M := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hWlo x.1])) (hM x)
      (abs_nonneg (F x)) (Real.exp_pos (θ*(N:ℝ))).le
  have hFI' : Integrable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      Real.exp (-θ*balanced i C b x.1)*F x) (EntryIIDCentral.rowLaw R N) :=
    Integrable.of_bound
      (((((measurable_balanced i C b).comp measurable_fst).const_mul (-θ)).exp).mul hF).aestronglyMeasurable
      (Real.exp (θ*N)*M)
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  rw [EntryIIDCentral.rowLaw,integral_prod _ hFI,
    exact_reverse_iid_moment ν (RawMixedSource.demand (xi i) b) N (fun r => ∫ u : unitInterval,F (r,u)) θ (C:ℝ)
      (RawMixedSource.measurable_demand _ _)
      (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) hb)),
    EntryIIDCentral.rowLaw,integral_prod _ hFI']
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun r => by
    change Real.exp (-θ*balanced i C b r)*(∫ u : unitInterval,F (r,u))=
      ∫ u : unitInterval,Real.exp (-θ*balanced i C b r)*F (r,u)
    rw [integral_const_mul]

section WeightedError
universe u
variable {Ω : ℕ → Type u} [∀ m,MeasurableSpace (Ω m)]
    (P : (m : ℕ) → Measure (Ω m)) [∀ m,IsProbabilityMeasure (P m)]

theorem relative_weighted_error
    (N : ℕ → ℕ) (hNp : ∀ m,0 < N m) (hN : Tendsto N atTop atTop)
    (θ : ℕ → ℝ) (hθ : ∀ m,θ m∈Icc (0:ℝ) 1)
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    (W Z F : (m : ℕ) → Ω m → ℝ)
    (hW : ∀ m,Measurable (W m)) (hZ : ∀ m,Measurable (Z m)) (hF : ∀ m,Measurable (F m))
    (k : ℕ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hZb : ∀ m x,Z m x∈Icc (0:ℝ) ((N m:ℝ)^k))
    (hFb : ∀ m x,F m x∈Icc (0:ℝ) (B*(N m:ℝ)^k))
    (hZzero : ∀ m x,W m x ≤ 0 → Z m x=0)
    (hFzero : ∀ m x,W m x ≤ 0 → F m x=0)
    (E : (m : ℕ) → Set (Ω m)) (hE : ∀ m,MeasurableSet (E m))
    (hbad : ∀ m,(P m).real (E m)ᶜ ≤ C*Real.exp (-2*Real.sqrt (N m:ℝ)))
    (e : ℕ → ℝ) (he0 : ∀ m,0 ≤ e m) (he : Tendsto e atTop (𝓝 0))
    (hcore : ∀ᶠ m in atTop,∀ᵐ x ∂P m,x∈E m → W m x ≤ radius (N m)*(N m:ℝ) →
      F m x ≤ e m*Z m x)
    {L : ℝ} (hmain : Tendsto (fun m => (N m:ℝ)*θ m^(k+2)*
      (∫ x,Real.exp (-θ m*W m x)*Z m x ∂P m)) atTop (𝓝 L)) :
    Tendsto (fun m => (N m:ℝ)*θ m^(k+2)*
      (∫ x,Real.exp (-θ m*W m x)*F m x ∂P m)) atTop (𝓝 0) := by
  classical
  have hweighted {m : ℕ} (J : Ω m → ℝ) {M : ℝ}
      (hb : ∀ x,J x∈Icc (0:ℝ) M) (hz : ∀ x,W m x ≤ 0 → J x=0) (x : Ω m) :
      (Real.exp (-θ m*W m x)*J x)∈Icc (0:ℝ) M := by
    constructor
    · exact mul_nonneg (Real.exp_pos _).le (hb x).1
    · by_cases hw : 0 < W m x
      · have he : Real.exp (-θ m*W m x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [(hθ m).1])
        exact (mul_le_mul_of_nonneg_right he (hb x).1).trans (by simpa using (hb x).2)
      · simp only [hz x (le_of_not_gt hw),mul_zero]
        exact (hb x).1.trans (hb x).2
  have hZI (m : ℕ) : Integrable (fun x => Real.exp (-θ m*W m x)*Z m x) (P m) :=
    Integrable.of_mem_Icc 0 ((N m:ℝ)^k)
      (((hW m).const_mul (-θ m)).exp.mul (hZ m)).aemeasurable
        (ae_of_all _ (hweighted (Z m) (hZb m) (hZzero m)))
  have hFI (m : ℕ) : Integrable (fun x => Real.exp (-θ m*W m x)*F m x) (P m) :=
    Integrable.of_mem_Icc 0 (B*(N m:ℝ)^k)
      (((hW m).const_mul (-θ m)).exp.mul (hF m)).aemeasurable
        (ae_of_all _ (hweighted (F m) (hFb m) (hFzero m)))
  have hlimMain : Tendsto (fun m => e m*((N m:ℝ)*θ m^(k+2)*
      (∫ x,Real.exp (-θ m*W m x)*Z m x ∂P m))) atTop (𝓝 0) := by
    simpa using he.mul hmain
  have hlimBad : Tendsto (fun m => (B*C)*((N m:ℝ)^(k+1)*Real.exp (-2*Real.sqrt (N m:ℝ))))
      atTop (𝓝 0) := by simpa using (polynomial_radius_tail N hN (k+1)).const_mul (B*C)
  have hlimTail : Tendsto (fun m => B*((N m:ℝ)^(k+1)*
      Real.exp (-θ m*(radius (N m)*(N m:ℝ))))) atTop (𝓝 0) := by
    simpa using (moderate_wide_tail N hNp hN θ hθN (k+1)).const_mul B
  have hlim := (hlimMain.add hlimBad).add hlimTail
  apply squeeze_zero' (Eventually.of_forall fun m => by
    have := (hθ m).1
    exact mul_nonneg (by positivity) (integral_nonneg fun x => (hweighted (F m) (hFb m) (hFzero m) x).1)) ?_
    (by simpa using hlim)
  filter_upwards [hcore] with m hm
  let T := radius (N m)*(N m:ℝ)
  have hpoint : ∀ᵐ x ∂P m,Real.exp (-θ m*W m x)*F m x ≤
      e m*(Real.exp (-θ m*W m x)*Z m x)+
        (if x∈E m then 0 else B*(N m:ℝ)^k)+
          B*(N m:ℝ)^k*Real.exp (-θ m*T) := by
    filter_upwards [hm] with x hx
    have hleft := hweighted (F m) (hFb m) (hFzero m) x
    have hzleft := hweighted (Z m) (hZb m) (hZzero m) x
    by_cases hxe : x∈E m
    · rw [if_pos hxe,add_zero]
      by_cases hw : W m x ≤ T
      · have hh := mul_le_mul_of_nonneg_left (hx hxe hw) (Real.exp_pos (-θ m*W m x)).le
        have hh' : Real.exp (-θ m*W m x)*F m x ≤
            e m*(Real.exp (-θ m*W m x)*Z m x) := by
          simpa only [mul_left_comm,mul_assoc] using hh
        exact hh'.trans (le_add_of_nonneg_right (by positivity))
      · have htail : Real.exp (-θ m*W m x)*F m x ≤
          B*(N m:ℝ)^k*Real.exp (-θ m*T) := by
          have he := Real.exp_le_exp.mpr (show -θ m*W m x ≤ -θ m*T by nlinarith [(hθ m).1,le_of_lt (lt_of_not_ge hw)])
          have hh := mul_le_mul he (hFb m x).2 (hFb m x).1 (Real.exp_pos _).le
          simpa [mul_comm] using hh
        exact htail.trans (le_add_of_nonneg_left (mul_nonneg (he0 m) hzleft.1))
    · rw [if_neg hxe]
      have hpos : 0 ≤ B*(N m:ℝ)^k*Real.exp (-θ m*T) := by positivity
      exact hleft.2.trans (by linarith [mul_nonneg (he0 m) hzleft.1])
  have hIB : Integrable (fun x : Ω m => if x∈E m then 0 else B*(N m:ℝ)^k) (P m) := by
    have hfun : (fun x : Ω m => if x∈E m then 0 else B*(N m:ℝ)^k)=
        (E m)ᶜ.indicator (fun _ => B*(N m:ℝ)^k) := by
      funext x
      by_cases hx : x∈E m <;> simp [hx]
    rw [hfun]
    exact (integrable_const (μ := P m) (B*(N m:ℝ)^k)).indicator (hE m).compl
  have hIe : Integrable (fun x =>
      e m*(Real.exp (-θ m*W m x)*Z m x)+(if x∈E m then 0 else B*(N m:ℝ)^k)) (P m) :=
    ((hZI m).const_mul (e m)).add hIB
  have hIR : Integrable (fun x =>
      e m*(Real.exp (-θ m*W m x)*Z m x)+(if x∈E m then 0 else B*(N m:ℝ)^k)+
        B*(N m:ℝ)^k*Real.exp (-θ m*T)) (P m) :=
    (((hZI m).const_mul (e m)).add hIB).add
      (integrable_const (B*(N m:ℝ)^k*Real.exp (-θ m*T)))
  have hint := integral_mono_ae (hFI m) hIR hpoint
  rw [integral_add hIe (integrable_const (B*(N m:ℝ)^k*Real.exp (-θ m*T))),
    integral_add ((hZI m).const_mul (e m)) hIB,integral_const_mul,
    integral_const,probReal_univ,one_smul] at hint
  have hbadint : (∫ x : Ω m,if x∈E m then 0 else B*(N m:ℝ)^k ∂P m)=
      B*(N m:ℝ)^k*(P m).real (E m)ᶜ := by
    rw [show (fun x : Ω m => if x∈E m then 0 else B*(N m:ℝ)^k)=
      (E m)ᶜ.indicator (fun _ => B*(N m:ℝ)^k) by ext x; by_cases hx : x∈E m <;> simp [hx],
      integral_indicator (hE m).compl,integral_const]
    simp [Measure.real,Measure.restrict_apply MeasurableSet.univ,mul_comm]
  rw [hbadint] at hint
  have hnorm : 0 ≤ (N m:ℝ)*θ m^(k+2) := by
    have := (hθ m).1
    positivity
  have hnormN : (N m:ℝ)*θ m^(k+2) ≤ N m := by
    have hh := pow_le_pow_left₀ (hθ m).1 (hθ m).2 (k+2)
    simpa using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (N m))
  have hbadterm := mul_le_mul_of_nonneg_left (hbad m) (show 0 ≤ B*(N m:ℝ)^k by positivity)
  have hupper : (∫ x,Real.exp (-θ m*W m x)*F m x ∂P m) ≤
      e m*(∫ x,Real.exp (-θ m*W m x)*Z m x ∂P m)+
        B*(N m:ℝ)^k*(C*Real.exp (-2*Real.sqrt (N m:ℝ)))+
          B*(N m:ℝ)^k*Real.exp (-θ m*T) := by linarith [hbadterm]
  have hscaled := mul_le_mul_of_nonneg_left hupper hnorm
  have hboth : 0 ≤ B*(N m:ℝ)^k*(C*Real.exp (-2*Real.sqrt (N m:ℝ)))+
      B*(N m:ℝ)^k*Real.exp (-θ m*T) := by positivity
  have hmN := mul_le_mul_of_nonneg_right hnormN hboth
  dsimp [T] at *
  have hid : (N m:ℝ)*(B*(N m:ℝ)^k*(C*Real.exp (-2*Real.sqrt (N m:ℝ)))+
      B*(N m:ℝ)^k*Real.exp (-θ m*(radius (N m)*(N m:ℝ))))=
      (B*C)*((N m:ℝ)^(k+1)*Real.exp (-2*Real.sqrt (N m:ℝ)))+
        B*((N m:ℝ)^(k+1)*Real.exp (-θ m*(radius (N m)*(N m:ℝ)))) := by
    rw [pow_succ]
    ring
  rw [hid] at hmN
  simp only [neg_mul] at hscaled hmN ⊢
  nlinarith only [hscaled,hmN]

end WeightedError
end FCAppendix.Affine.Uniform06.EntryRelativeWeight
