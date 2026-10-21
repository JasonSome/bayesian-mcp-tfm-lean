import FCAppendix.Affine.LowBody.ClusterLimitContraction

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical

theorem atom_contraction_of_actual_cluster_estimates
    (H G : ℕ→ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    {κ A D C L : ℝ} (hκ : 0≤κ) (hA : 0<A) (hD : 0≤D) (hC : 0≤C)
    (eps : ℕ→ℝ) (heps0 : Tendsto eps atTop (𝓝 0))
    (hfinite : ∀b : ℝ,0<b→∀err : ℝ,0<err→∃δmax>0,
      ∀δ : ℝ,0<δ→δ<b→δ<δmax→∀ᶠj : ℕ in atTop,
        (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))^2*((b-δ)*A-eps j*L)≤
        (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))*
          ((b+3*δ)*D*((G j : Measure ℝ).real (Icc (b-δ) (b+3*δ))+
            (G j : Measure ℝ).real (Icc (κ*(b-δ)) (κ*(b+3*δ))))+C*δ+err)) :
    ∀b : ℝ,0<b→(G₀ : Measure ℝ).real {b}≤
      (D/A)*((G₀ : Measure ℝ).real {b}+(G₀ : Measure ℝ).real {κ*b}) := by
  intro b hb
  let r : ℕ→ℝ:=fun j=>1/((j:ℝ)+1)
  have hrpos (j : ℕ) : 0<r j:=by dsimp [r]; positivity
  have hranti : Antitone r := by
    intro i j hij
    dsimp [r]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hrt : Tendsto r atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  apply atom_bound_of_shrinking_envelopes (G₀ : Measure ℝ) hb hA r
    (fun j=>(hrpos j).le) hranti hrt hκ
  apply Eventually.of_forall
  intro k
  obtain ⟨δmax,hδmax,hf⟩:=hfinite b hb (r k) (hrpos k)
  let δ:=min (r k) (min (b/2) (δmax/2))
  have hδ : 0<δ:=lt_min (hrpos k) (lt_min (half_pos hb) (half_pos hδmax))
  have hδr : δ≤r k:=min_le_left _ _
  have hδb : δ<b:=(min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (half_lt_self hb))
  have hδmax' : δ<δmax:=(min_le_right _ _).trans_lt
    ((min_le_right _ _).trans_lt (half_lt_self hδmax))
  have hAδ : 0<(b-δ)*A:=mul_pos (sub_pos.mpr hδb) hA
  have hDδ : 0≤(b+3*δ)*D:=mul_nonneg (by linarith) hD
  have heδ : 0≤C*δ+r k:=add_nonneg (mul_nonneg hC hδ.le) (hrpos k).le
  have hmass:=atom_bound_of_varying_finite_cluster_estimates H G G₀ hH hG
    (Ioo (b-δ) (b+δ)) (Icc (b-δ) (b+3*δ)) (Icc (κ*(b-δ)) (κ*(b+3*δ)))
    isOpen_Ioo isClosed_Icc isClosed_Icc b ((b-δ)*A) ((b+3*δ)*D) (C*δ+r k)
    ⟨by linarith,by linarith⟩ hAδ hDδ heδ
    (fun j=>(b-δ)*A-eps j*L) (fun _=>(b+3*δ)*D) (fun _=>C*δ+r k)
    (by simpa using (tendsto_const_nhds (x:=(b-δ)*A)).sub (heps0.mul_const L))
    tendsto_const_nhds tendsto_const_nhds (by simpa only [add_assoc] using hf δ hδ hδb hδmax')
  have hB : (G₀ : Measure ℝ).real (Icc (b-δ) (b+3*δ))≤
      (G₀ : Measure ℝ).real (Icc (b-3*r k) (b+3*r k)) := by
    refine measureReal_mono ?_ (measure_ne_top (G₀ : Measure ℝ) _)
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hC' : (G₀ : Measure ℝ).real (Icc (κ*(b-δ)) (κ*(b+3*δ)))≤
      (G₀ : Measure ℝ).real (Icc (κ*b-3*κ*r k) (κ*b+3*κ*r k)) := by
    refine measureReal_mono ?_ (measure_ne_top (G₀ : Measure ℝ) _)
    intro x hx
    have hh:=mul_le_mul_of_nonneg_left hδr hκ
    have hkr:=mul_nonneg hκ (hrpos k).le
    constructor <;> nlinarith [hx.1,hx.2]
  have hleft : (G₀ : Measure ℝ).real {b}*((b-r k)*A)≤
      (G₀ : Measure ℝ).real {b}*((b-δ)*A) := by
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    exact mul_le_mul_of_nonneg_right (by linarith) hA.le
  have hcoef : (b+3*δ)*D≤(b+3*r k)*D:=
    mul_le_mul_of_nonneg_right (by linarith) hD
  have hrhs : (b+3*δ)*D*((G₀ : Measure ℝ).real (Icc (b-δ) (b+3*δ))+
      (G₀ : Measure ℝ).real (Icc (κ*(b-δ)) (κ*(b+3*δ))))≤
      (b+3*r k)*D*((G₀ : Measure ℝ).real (Icc (b-3*r k) (b+3*r k))+
      (G₀ : Measure ℝ).real (Icc (κ*b-3*κ*r k) (κ*b+3*κ*r k))) := by
    exact mul_le_mul hcoef (add_le_add hB hC') (add_nonneg measureReal_nonneg measureReal_nonneg)
      (mul_nonneg (by linarith [hrpos k]) hD)
  have herr : C*δ+r k≤(C+1)*r k := by
    have hh:=mul_le_mul_of_nonneg_left hδr hC
    linarith
  exact hleft.trans (hmass.trans (add_le_add hrhs herr))

theorem no_positive_atoms_of_actual_cluster_estimates
    (H G : ℕ→ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    {κ A D C L : ℝ} (hκ : 0<κ) (hA : 0<A) (hD : 0≤D) (hC : 0≤C)
    (hsmall : D/A<1/2) (eps : ℕ→ℝ) (heps0 : Tendsto eps atTop (𝓝 0))
    (hfinite : ∀b : ℝ,0<b→∀err : ℝ,0<err→∃δmax>0,
      ∀δ : ℝ,0<δ→δ<b→δ<δmax→∀ᶠj : ℕ in atTop,
        (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))^2*((b-δ)*A-eps j*L)≤
        (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))*
          ((b+3*δ)*D*((G j : Measure ℝ).real (Icc (b-δ) (b+3*δ))+
            (G j : Measure ℝ).real (Icc (κ*(b-δ)) (κ*(b+3*δ))))+C*δ+err)) :
    ∀b : ℝ,0<b→(G₀ : Measure ℝ) {b}=0 :=
  no_positive_atoms_of_cluster_bound (G₀ : Measure ℝ) hκ (div_nonneg hD hA.le) hsmall
    (atom_contraction_of_actual_cluster_estimates H G G₀ hH hG hκ.le hA hD hC eps heps0 hfinite)

end FCAppendix.Affine.LowBody
