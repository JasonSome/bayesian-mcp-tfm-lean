import FCAppendix.Affine.Uniform07Finishing.Crossover.SupportGaps

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set MeasureTheory Filter Topology

theorem exists_safe_point_of_long_below_interval
    {S : Set ℝ} {delta T : ℝ → ℝ} {L b m mu K upper : ℝ}
    (hS : IsClosed S) (hLb : L≤ b) (hbS : b∈S)
    (hm : 0< m) (hmu : 0< mu)
    (hAC : AbsolutelyContinuousOnInterval delta L b)
    (hreset : ∀ x y, L≤ x → x< y → y≤ b → y∈S →
      (∀ z∈Ioo x y, z∉S) → upper< delta y-T y)
    (hbelow : ∀ x∈Icc L b, x∈S → delta x-T x≤ upper →
      0≤ delta x ∧ delta x≤ K/m)
    (hder : ∀ᵐ x ∂volume, x∈Icc L b → x∈S → delta x-T x≤ upper →
      mu≤ deriv delta x)
    (hlength : K/(mu*m)< b-L) :
    ∃ a∈Icc L b, upper≤ delta a-T a := by
  by_contra hnone
  have hnegative : ∀ x∈Icc L b, delta x-T x< upper := by
    intro x hx
    exact lt_of_not_ge (fun h => hnone ⟨x,hx,h⟩)
  have hused : Icc L b ⊆ S := negative_segment_has_no_gaps hS hLb hbS
    (fun x hx => hnegative x ⟨hx.1.le,hx.2⟩) hreset
  have hder' : ∀ᵐ x ∂volume.restrict (Icc L b), mu≤ deriv delta x := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hder] with x hx hxb
    exact hx hxb (hused hxb) (hnegative x hxb).le
  have hinc := ac_increment_lower hLb hAC hder'
  have hleft := hbelow L ⟨le_rfl,hLb⟩ (hused ⟨le_rfl,hLb⟩)
    (hnegative L ⟨le_rfl,hLb⟩).le
  have hright := hbelow b ⟨hLb,le_rfl⟩ hbS (hnegative b ⟨hLb,le_rfl⟩).le
  have hwidth : b-L≤ K/(mu*m) := by
    apply (le_div_iff₀ (mul_pos hmu hm)).2
    have hbound : mu*(b-L)≤ K/m := by linarith
    have hmBound := (le_div_iff₀ hm).mp hbound
    nlinarith
  exact (not_le_of_gt hlength) hwidth

theorem finite_closed_support_barrier_after_overlap
    {S : Set ℝ} {delta T weight H : ℝ→ℝ}
    {L R m eps mu K k err omega : ℝ}
    (hS : IsClosed S) (hLR : L≤ R)
    (hm : 0< m) (heps : 0< eps) (hmu : 0< mu)
    (hk : 0≤ k) (homega : 0≤ omega)
    (hF : ContinuousOn (fun x => delta x-T x) (Icc L R))
    (hDeltaAC : AbsolutelyContinuousOnInterval delta L R)
    (hWeightAC : AbsolutelyContinuousOnInterval weight L R)
    (hreset : ∀ x y, L≤ x → x< y → y≤ R → y∈S →
      (∀ z∈Ioo x y, z∉S) → -eps/(2*m)< delta y-T y)
    (hbelowBounds : ∀ x∈Icc L R, x∈S →
      delta x-T x≤-eps/(2*m) → 0≤ delta x ∧ delta x≤ K/m)
    (hbelowDeriv : ∀ᵐ x ∂volume, x∈Icc L R → x∈S →
      delta x-T x≤-eps/(2*m) →
      mu≤ deriv delta x ∧ deriv weight x≤ 0)
    (hweight : ∀ x∈Icc L R, weight x∈Icc (0:ℝ) 1)
    (hHpos : ∀ x∈Icc L R, 0≤ H x)
    (hlead : ∀ x∈Icc L R,
      |m*T x-(1+k*weight x)*H x|≤ err)
    (hmodulus : ∀ a∈Icc L R, ∀ b∈Icc L R,
      a≤ b → b-a≤ K/(mu*m) → |H b-H a|≤ omega)
    (hsmall : (1+k)*omega+2*err< eps/2) :
    ∀ b∈Icc L R, b∈S → K/(mu*m)< b-L → T b-eps/m< delta b := by
  intro b hb hbS hlong
  have hsubLb : uIcc L b ⊆ uIcc L R := by
    rw [uIcc_of_le hb.1,uIcc_of_le hLR]
    exact fun x hx => ⟨hx.1,hx.2.trans hb.2⟩
  obtain ⟨a,ha,hstart⟩ := exists_safe_point_of_long_below_interval hS hb.1 hbS hm hmu
    (hDeltaAC.mono hsubLb)
    (fun x y hLx hxy hyb hyS hgap =>
      hreset x y hLx hxy (hyb.trans hb.2) hyS hgap)
    (fun x hx hxS hxF => hbelowBounds x ⟨hx.1,hx.2.trans hb.2⟩ hxS hxF)
    (by
      filter_upwards [hbelowDeriv] with x hx hxb hxS hxF
      exact (hx ⟨hxb.1,hxb.2.trans hb.2⟩ hxS hxF).1)
    hlong
  have hsub : Icc a b ⊆ Icc L R := fun x hx =>
    ⟨ha.1.trans hx.1,hx.2.trans hb.2⟩
  have husub : uIcc a b ⊆ uIcc L R := by
    simpa only [uIcc_of_le ha.2,uIcc_of_le hLR] using hsub
  apply finite_closed_support_barrier hS ha.2 hm heps hmu hk homega
    (hF.mono hsub) (hDeltaAC.mono husub) (hWeightAC.mono husub) hstart
    (fun x y hax hxy hyb hyS hgap =>
      hreset x y (ha.1.trans hax) hxy (hyb.trans hb.2) hyS hgap)
    (fun x hx hxS hxF => hbelowBounds x (hsub hx) hxS hxF.2)
    (by
      filter_upwards [hbelowDeriv] with x hx hxab hxS hxF
      exact hx (hsub hxab) hxS hxF.2)
    (fun x hx => hweight x (hsub hx)) (fun x hx => hHpos x (hsub hx))
    (fun x hx => hlead x (hsub hx))
    (fun x hx y hy hxy hwidth => hmodulus x (hsub hx) y (hsub hy) hxy hwidth)
    hsmall b ⟨ha.2,le_rfl⟩ hbS

end FCAppendix.Affine.Uniform07Finishing.Crossover
