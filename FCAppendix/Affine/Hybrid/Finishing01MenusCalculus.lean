import FCAppendix.Affine.Hybrid.ActiveMenuEndpointSigns

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finishing01Menus
open Set Filter Topology

def bidMenu (ξ z v lam b : ℝ) : ℝ :=
  z*(v-b)+(1-z)*(v*(2*exposure ξ lam b-(exposure ξ lam b)^2)-
    2*lam*exposure ξ lam b)

theorem bidMenu_eq_two {ξ z v lam b : ℝ}
    (hξ : ξ≠0) (hlam : lam≠0) (hb : b≠0) :
    bidMenu ξ z v lam b=two ξ z v lam (exposure ξ lam b) := by
  have he : 1-ξ*exposure ξ lam b=lam/b := by
    unfold exposure
    field_simp
    ring
  have hi : lam/(1-ξ*exposure ξ lam b)=b := by
    rw [he]
    field_simp
  simp only [bidMenu,two,hi]

theorem bidMenu_eq_physical {ξ η z v lam b : ℝ}
    (hη : η=1-2*ξ) (hξ : ξ≠0) (hb : b≠0) :
    bidMenu ξ z v lam b=
      z*(v-b)+(1-z)*independentTwo η v b (exposure ξ lam b) := by
  have he := independentTwo_eq_menu (lam:=lam) (v:=v) hη hξ hb
  simp only [two,zero_mul,sub_zero,one_mul,zero_add] at he
  rw [bidMenu,he]

theorem hasDerivAt_exposure {ξ lam b : ℝ} (hξ : ξ≠0) (hb : b≠0) :
    HasDerivAt (exposure ξ lam) (lam/(ξ*b^2)) b := by
  have hh := ((hasDerivAt_const b (1:ℝ)).sub
    ((hasDerivAt_const b lam).div (hasDerivAt_id b) hb)).div_const ξ
  apply hh.congr_deriv
  dsimp only [id_eq]
  field_simp [hξ,hb]
  ring

theorem hasDerivAt_bidMenu {ξ z v lam b : ℝ} (hξ : ξ≠0) (hb : b≠0) :
    HasDerivAt (bidMenu ξ z v lam) (bidDerivative ξ z v lam b) b := by
  have hq := hasDerivAt_exposure (lam:=lam) hξ hb
  have hh := (((hasDerivAt_const b v).sub (hasDerivAt_id b)).const_mul z).add
    (((((hq.const_mul 2).sub (hq.pow 2)).const_mul v).sub
      (hq.const_mul (2*lam))).const_mul (1-z))
  apply hh.congr_deriv
  unfold bidDerivative
  ring

theorem continuousOn_bidDerivative (ξ z : ℝ) (hξ : ξ≠0)
    {L U : ℝ} (hL : 0< L) :
    ContinuousOn (fun p : (ℝ×ℝ)×ℝ => bidDerivative ξ z p.1.1 p.1.2 p.2)
      (univ ×ˢ Icc L U) := by
  intro p hp
  have hb : p.2≠0 := (hL.trans_le hp.2.1).ne'
  have hd : ξ*p.2^2≠0 := mul_ne_zero hξ (pow_ne_zero 2 hb)
  unfold bidDerivative exposure
  fun_prop

theorem primitive_box_nonempty {ξ z qbar L U vlo vhi : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hz : 0≤ z) (hz1 : z<1)
    (hq : qbar∈ Ioo (0:ℝ) 1) (hv : vlo≤ vhi)
    (hlo : L < inwardScale ξ z qbar*vlo)
    (hhi : inwardScale ξ z qbar*vhi< U) : L< U := by
  have hT := inwardScale_pos hξ hξ1 hz hz1 hq
  exact (hlo.trans_le (mul_le_mul_of_nonneg_left hv hT.le)).trans hhi

theorem exists_uniform_endpoint_strips {ξ z qbar L U vlo vhi : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hz : 0≤ z) (hz1 : z<1)
    (hq : qbar∈ Ioo (0:ℝ) 1) (hL : 0< L) (hvv : vlo≤ vhi)
    (hUv : U< vlo)
    (hlo : L < inwardScale ξ z qbar*vlo)
    (hhi : inwardScale ξ z qbar*vhi< U) :
    ∃τ c : ℝ, 0<τ ∧ 4*τ< U-L ∧ 0< c ∧
      L+2*τ∈ Icc L U ∧ U-2*τ∈ Icc L U ∧
      ∀ v∈ Icc vlo vhi,
      ∀ lam∈ Icc ((1-ξ*qbar)*L) ((1-ξ*qbar)*U),
        (∀ b∈ Icc L (L+τ),
          bidMenu ξ z v lam b+c≤ bidMenu ξ z v lam (L+2*τ)) ∧
        (∀ b∈ Icc (U-τ) U,
          bidMenu ξ z v lam b+c≤ bidMenu ξ z v lam (U-2*τ)) := by
  have hLU := primitive_box_nonempty hξ hξ1 hz hz1 hq hvv hlo hhi
  have h0 : 0<1-ξ*qbar := by nlinarith [hq.2]
  let K : Set (ℝ×ℝ) := Icc vlo vhi ×ˢ
    Icc ((1-ξ*qbar)*L) ((1-ξ*qbar)*U)
  let D : ℝ×ℝ → ℝ := fun p => min
    (bidDerivative ξ z p.1 p.2 L) (-bidDerivative ξ z p.1 p.2 U)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKn : K.Nonempty := ⟨(vlo,(1-ξ*qbar)*L),
    ⟨⟨le_rfl,hvv⟩,⟨le_rfl,mul_le_mul_of_nonneg_left hLU.le h0.le⟩⟩⟩
  have hU : 0< U := hL.trans hLU
  have hDc : Continuous D := by
    have hLn : L≠0 := hL.ne'
    have hUn : U≠0 := hU.ne'
    dsimp [D]
    unfold bidDerivative exposure
    fun_prop
  obtain ⟨p0,hp0,hmin⟩ := hK.exists_isMinOn hKn hDc.continuousOn
  have hDpos : 0< D p0 := by
    have hs := active_menu_endpoint_signs hξ hξ1 hz hz1 hq hL hLU.le
      hUv hlo hhi hp0.1 hp0.2
    exact lt_min hs.1 (neg_pos.mpr hs.2)
  have hDmin (v lam : ℝ) (hv : v∈ Icc vlo vhi)
      (hlam : lam∈ Icc ((1-ξ*qbar)*L) ((1-ξ*qbar)*U)) :
      D p0≤ bidDerivative ξ z v lam L ∧
        bidDerivative ξ z v lam U≤-D p0 := by
    have hh := hmin (show (v,lam)∈ K from ⟨hv,hlam⟩)
    change D p0≤ min _ _ at hh
    exact ⟨hh.trans (min_le_left _ _), by linarith [hh.trans (min_le_right _ _)]⟩
  let S : Set ((ℝ×ℝ)×ℝ) := K ×ˢ Icc L U
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : (ℝ×ℝ)×ℝ => bidDerivative ξ z p.1.1 p.1.2 p.2) S :=
    (continuousOn_bidDerivative ξ z hξ.ne' hL).mono
      (fun _ hp => ⟨mem_univ _,hp.2⟩)
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hcont) (D p0/2) (half_pos hDpos)
  let τ := min ((U-L)/8) (δ/4)
  have hτ : 0<τ := lt_min (by linarith) (by linarith)
  have hτwidth : 4*τ< U-L := by
    have h := min_le_left ((U-L)/8) (δ/4)
    dsimp only [τ] at *
    linarith
  have hτδ : 2*τ<δ := by
    have h := min_le_right ((U-L)/8) (δ/4)
    dsimp only [τ] at *
    linarith
  have hlowtarget : L+2*τ∈ Icc L U := ⟨by linarith,by linarith⟩
  have hightarget : U-2*τ∈ Icc L U := ⟨by linarith,by linarith⟩
  have hnearL (v lam x : ℝ) (hv : v∈ Icc vlo vhi)
      (hlam : lam∈ Icc ((1-ξ*qbar)*L) ((1-ξ*qbar)*U))
      (hx : x∈ Icc L (L+2*τ)) :
      D p0/2≤ bidDerivative ξ z v lam x := by
    have hxU : x≤ U := hx.2.trans hlowtarget.2
    have hh := hmod ((v,lam),x) ⟨⟨hv,hlam⟩,hx.1,hxU⟩
      ((v,lam),L) ⟨⟨hv,hlam⟩,le_rfl,hLU.le⟩
    have hdist : dist ((v,lam),x) ((v,lam),L)<δ := by
      simp only [Prod.dist_eq,dist_self,Real.dist_eq,
        max_eq_right (abs_nonneg (x-L))]
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    have he := abs_lt.mp (show |bidDerivative ξ z v lam x-
      bidDerivative ξ z v lam L|< D p0/2 by
      simpa only [Real.dist_eq] using hh hdist)
    linarith [(hDmin v lam hv hlam).1]
  have hnearU (v lam x : ℝ) (hv : v∈ Icc vlo vhi)
      (hlam : lam∈ Icc ((1-ξ*qbar)*L) ((1-ξ*qbar)*U))
      (hx : x∈ Icc (U-2*τ) U) :
      bidDerivative ξ z v lam x≤-(D p0/2) := by
    have hxL : L≤ x := hightarget.1.trans hx.1
    have hh := hmod ((v,lam),x) ⟨⟨hv,hlam⟩,hxL,hx.2⟩
      ((v,lam),U) ⟨⟨hv,hlam⟩,hLU.le,le_rfl⟩
    have hdist : dist ((v,lam),x) ((v,lam),U)<δ := by
      simp only [Prod.dist_eq,dist_self,Real.dist_eq,
        max_eq_right (abs_nonneg (x-U))]
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith [hx.1]
    have he := abs_lt.mp (show |bidDerivative ξ z v lam x-
      bidDerivative ξ z v lam U|< D p0/2 by
      simpa only [Real.dist_eq] using hh hdist)
    linarith [(hDmin v lam hv hlam).2]
  refine ⟨τ,D p0*τ/2,hτ,hτwidth,by positivity,hlowtarget,hightarget,?_⟩
  intro v hv lam hlam
  constructor
  · intro b hb
    have hbtarget : b< L+2*τ := by linarith [hb.2]
    have hf (x : ℝ) (hx : x∈ Icc b (L+2*τ)) :
        HasDerivAt (bidMenu ξ z v lam) (bidDerivative ξ z v lam x) x :=
      hasDerivAt_bidMenu hξ.ne' ((hL.trans_le hb.1).trans_le hx.1).ne'
    obtain ⟨x,hx,hslope⟩ := exists_hasDerivAt_eq_slope
      (bidMenu ξ z v lam) (bidDerivative ξ z v lam) hbtarget
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
    have hd := hnearL v lam x hv hlam ⟨hb.1.trans hx.1.le,hx.2.le⟩
    rw [hslope] at hd
    have hgap := (le_div_iff₀ (sub_pos.mpr hbtarget)).mp hd
    have hdist : τ≤ L+2*τ-b := by linarith [hb.2]
    have hg := mul_le_mul_of_nonneg_left hdist (half_pos hDpos).le
    nlinarith
  · intro b hb
    have htargetb : U-2*τ< b := by linarith [hb.1]
    have hf (x : ℝ) (hx : x∈ Icc (U-2*τ) b) :
        HasDerivAt (bidMenu ξ z v lam) (bidDerivative ξ z v lam x) x :=
      hasDerivAt_bidMenu hξ.ne' ((hL.trans_le hightarget.1).trans_le hx.1).ne'
    obtain ⟨x,hx,hslope⟩ := exists_hasDerivAt_eq_slope
      (bidMenu ξ z v lam) (bidDerivative ξ z v lam) htargetb
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
    have hd := hnearU v lam x hv hlam ⟨hx.1.le,hx.2.le.trans hb.2⟩
    rw [hslope] at hd
    have hgap := (div_le_iff₀ (sub_pos.mpr htargetb)).mp hd
    have hdist : τ≤ b-(U-2*τ) := by linarith [hb.1]
    have hg := mul_le_mul_of_nonneg_left hdist (half_pos hDpos).le
    nlinarith

theorem exclude_strip_of_finite_gap {F R : ℝ→ℝ} {b target c ε : ℝ}
    (hc : 0< c) (hε : 3*ε< c)
    (hgap : R b+c≤ R target)
    (hinc : |F b-R b|≤ε) (hdev : |F target-R target|≤ε)
    (hIC : F target≤ F b) : False := by
  have hi := abs_le.mp hinc
  have hd := abs_le.mp hdev
  have he : 0≤ε := (abs_nonneg _).trans hinc
  linarith

theorem eventually_noise_below {U δ : ℝ} {ε : ℕ→ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : 0<δ) :
    ∀ᶠj in atTop, ε j*U<δ := by
  have hh : Tendsto (fun j => ε j*U) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε.mul_const U
  exact hh.eventually (gt_mem_nhds hδ)

end FCAppendix.Affine.Hybrid.Finishing01Menus
