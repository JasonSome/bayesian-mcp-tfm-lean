import FCAppendix.Affine.Hybrid.ClassifiedPolicy
import FCAppendix.Proposer.CommonListGame

noncomputable section
namespace FCAppendix.Appendix08.Tail
open MeasureTheory ProbabilityTheory Set Game Bayes Classical Affine
open scoped BigOperators

def tailB (xi : ℝ) : ℝ := 1 + xi / 50
def tailPartialFloor (xi : ℝ) : ℝ := 1 - 37 * xi / 40

theorem tail_partial_duplicate_gap (xi : ℝ) :
    tailPartialFloor xi - (1-xi)*tailB xi = xi*(11/200+xi/50) := by
  unfold tailPartialFloor tailB
  ring

theorem tail_partial_floor_guards {xi : ℝ} (hxi : 0< xi) (hxiHalf : xi<1/2) :
    0< tailPartialFloor xi ∧ tailPartialFloor xi<1 ∧
      1< tailB xi ∧ tailB xi<101/100 ∧
      (1-xi)*tailB xi< tailPartialFloor xi := by
  have hg := tail_partial_duplicate_gap xi
  have hx2 : 0< xi*(11/200+xi/50) := by positivity
  dsimp [tailPartialFloor,tailB] at hg ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem tail_rare_private_receipt_guard {xi e : ℝ}
    (hxi : 0< xi) (hxiHalf : xi<1/2) (he : e≤ 1/100) :
    (1-xi)*tailB xi + xi*tailB xi*e < tailPartialFloor xi := by
  have hB := (tail_partial_floor_guards hxi hxiHalf).2.2.1
  have hBmax := (tail_partial_floor_guards hxi hxiHalf).2.2.2.1
  have hmul : xi*tailB xi*e ≤ xi*tailB xi*(1/100) :=
    mul_le_mul_of_nonneg_left he (mul_nonneg hxi.le (by linarith))
  have hg := tail_partial_duplicate_gap xi
  have hsq := sq_nonneg xi
  unfold tailB at hBmax hmul hg ⊢
  unfold tailPartialFloor at hg ⊢
  nlinarith

theorem nonowner_receipt_bound {xi B b p e : ℝ}
    (hxi : 0≤ xi) (hxiOne : xi≤ 1) (hB : b≤ B)
    (hb : 0≤ b) (he : 0≤ e) (hp : 1-e≤ p) :
    b*(1-xi*p) ≤ (1-xi)*B + xi*B*e := by
  have hkap : 0≤ 1-xi := sub_nonneg.mpr hxiOne
  have h0 : 0≤ 1-xi+xi*e := add_nonneg hkap (mul_nonneg hxi he)
  have hp' : 1-xi*p≤ 1-xi+xi*e := by
    have hh := mul_le_mul_of_nonneg_left hp hxi
    nlinarith
  calc
    b*(1-xi*p) ≤ b*(1-xi+xi*e) := mul_le_mul_of_nonneg_left hp' hb
    _ ≤ B*(1-xi+xi*e) := mul_le_mul_of_nonneg_right hB h0
    _ = _ := by ring

theorem tail_nonowner_below_partial {xi b p e : ℝ}
    (hxi : 0< xi) (hxiHalf : xi<1/2)
    (hb0 : 0≤ b) (hbB : b≤ tailB xi)
    (he0 : 0≤ e) (he : e≤ 1/100) (hp : 1-e≤ p) :
    b*(1-xi*p)< tailPartialFloor xi := by
  exact (nonowner_receipt_bound hxi.le (by linarith) hbB hb0 he0 hp).trans_lt
    (tail_rare_private_receipt_guard hxi hxiHalf he)

theorem tail_high_above_low {xi d b p R : ℝ}
    (hxi : 0≤ xi) (hxiOne : xi<1) (hd : d<1-xi)
    (hb : 1≤ b) (hp : p≤ 1) (hdR : d< R) :
    d < b*(1-xi*p) ∧ ∀u : ℝ,R≤ u → d< u := by
  constructor
  · have hp' : 1-xi≤ 1-xi*p := by
      have hh := mul_le_mul_of_nonneg_left hp hxi
      nlinarith
    have hscale : 1-xi≤ b*(1-xi) := by
      have hh := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hxiOne.le)
      simpa only [one_mul] using hh
    have hmul : b*(1-xi)≤ b*(1-xi*p) :=
      mul_le_mul_of_nonneg_left hp' (by linarith)
    exact hd.trans_le (hscale.trans hmul)
  · intro u hu
    exact hdR.trans_le hu

theorem tail_central_partial_margins (xi : ℝ) :
    tailPartialFloor xi-(1-19*xi/20)=xi/40 ∧
      (1-9*xi/10)-tailPartialFloor xi=xi/40 := by
  unfold tailPartialFloor
  constructor <;> ring

theorem tail_first_copies_counts (N H0 H1 c : ℕ)
    (h0 : c≤ N+H0) (h1 : c≤ N+H1) (hfit : N+H0+H1≤ 2*c) :
    H0≤ c ∧ H1≤ c ∧
      let r0 := c-H0
      let r1 := c-H1
      let D := r0+r1-N
      D≤ r0 ∧ D≤ r1 ∧ D≤ N ∧
        (r0-D)+(r1-D)=N-D ∧
        H0+D+(r0-D)=c ∧ H1+D+(r1-D)=c := by
  constructor
  · omega
  constructor
  · omega
  dsimp
  omega

def tailOwnerLeft (N H0 c : ℕ) : ℕ := max (c-H0) (N-c)
def tailOwnerRight (N H0 c : ℕ) : ℕ := N-tailOwnerLeft N H0 c

theorem tail_overload_owner_counts (N H0 H1 c : ℕ)
    (h0 : c≤ N+H0) (h1 : c≤ N+H1)
    (hN : N≤ 2*c) (hover : 2*c≤ N+H0+H1) :
    tailOwnerLeft N H0 c+tailOwnerRight N H0 c=N ∧
      c-H0≤ tailOwnerLeft N H0 c ∧ tailOwnerLeft N H0 c≤ c ∧
      c-H1≤ tailOwnerRight N H0 c ∧ tailOwnerRight N H0 c≤ c := by
  dsimp [tailOwnerRight,tailOwnerLeft]
  omega

section Rank
variable {m : ℕ}

def eligibleList (E : Finset (Fin m)) (b : Fin m→ℝ) : LocalList m :=
  fun i=>if i∈E then some (b i) else none

def eligibleRank (E : Finset (Fin m)) (b : Fin m→ℝ) (c : ℕ) : Finset (Fin m) :=
  HighestBid.selection (eligibleList E b) c

theorem measurable_eligibleRank (E : Finset (Fin m)) (c : ℕ) :
    Measurable (fun b : Fin m→ℝ=>eligibleRank E b c) := by
  have hL : Measurable (fun b : Fin m→ℝ=>eligibleList E b) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi:i∈E
    · simpa only [eligibleList,if_pos hi,Function.comp_def] using
        measurable_some.comp (measurable_pi_apply i)
    · simpa only [eligibleList,if_neg hi] using
        (measurable_const : Measurable (fun _ : Fin m→ℝ=>(none : Option ℝ)))
  exact (HighestBid.measurable_selection m c).comp hL

theorem eligibleRank_subset (E : Finset (Fin m)) (b : Fin m→ℝ) (c : ℕ) :
    eligibleRank E b c ⊆ E := by
  intro i hi
  have hp := (HighestBid.selection_best (eligibleList E b) c).1.2 i hi
  by_contra hn
  exact hp (by simp [eligibleList,hn])

theorem eligibleRank_masked_optimal (E : Finset (Fin m)) (b : Fin m→ℝ) (c : ℕ) :
    Finite.Optimal c (fun i=>if i∈E then b i else 0) (eligibleRank E b c) := by
  have he : (fun i => entryBid (eligibleList E b i)) =
      (fun i => if i∈E then b i else 0) := by
    funext i
    by_cases hi : i∈E <;> simp [eligibleList,entryBid,hi]
  simpa only [eligibleRank,he] using
    HighestBid.selection_optimal (eligibleList E b) c

theorem eligibleRank_card (E : Finset (Fin m)) (b : Fin m→ℝ) (c : ℕ)
    (hcard : c≤ E.card) (hb : ∀i∈E,0< b i) :
    (eligibleRank E b c).card=c := by
  have ho := eligibleRank_masked_optimal E b c
  apply le_antisymm ho.1
  by_contra hn
  have hslt : (eligibleRank E b c).card< c := lt_of_not_ge hn
  have hnot : ¬E⊆eligibleRank E b c := by
    intro hsub
    have hh := Finset.card_le_card hsub
    omega
  obtain ⟨i,hiE,hiS⟩ := Finset.not_subset.mp hnot
  have hp : 0<(if i∈E then b i else 0) := by simp [hiE,hb i hiE]
  have hh := Finite.optimal_fills c _ _ ho i hiS hp
  omega

theorem eligibleRank_optimal (E : Finset (Fin m)) (b w : Fin m→ℝ) (c : ℕ)
    (hcard : c≤ E.card) (hb : ∀i∈E,0< b i)
    (hmatch : ∀i∈E,w i=b i) (hw : ∀i,0≤ w i)
    (horder : ∀i∈E,∀k∉E,w k≤ b i) :
    Finite.Optimal c w (eligibleRank E b c) := by
  apply Hybrid.priority_full_optimal c w E (eligibleRank E b c)
    (eligibleRank_subset E b c) (eligibleRank_card E b c hcard hb) hw
  · intro i hi k hk
    rw [hmatch i hi]
    exact horder i hi k hk
  · have he : (fun i=>if i∈E then w i else 0)=
        (fun i=>if i∈E then b i else 0) := by
      funext i
      by_cases hi:i∈E <;> simp [hi,hmatch i]
    rw [he]
    exact eligibleRank_masked_optimal E b c

theorem tail_overload_rank_optimal (E : Finset (Fin m)) (b w : Fin m→ℝ)
    (c : ℕ) (R : ℝ) (hR : 0< R) (hcard : c≤ E.card)
    (hb : ∀i∈E,R≤ b i) (hmatch : ∀i∈E,w i=b i)
    (hw : ∀i,0≤ w i) (hout : ∀i∉E,w i≤ R) :
    Finite.Optimal c w (eligibleRank E b c) := by
  apply eligibleRank_optimal E b w c hcard
    (fun i hi=>hR.trans_le (hb i hi)) hmatch hw
  intro i hi k hk
  exact (hout k hk).trans (hb i hi)

theorem tail_top_owners_rank_optimal (E : Finset (Fin m)) (b w : Fin m→ℝ)
    (c : ℕ) (ell : ℝ) (hell : 0< ell) (hcard : c≤ E.card)
    (hb : ∀i∈E,ell≤ b i) (hmatch : ∀i∈E,w i=b i)
    (hw : ∀i,0≤ w i) (hout : ∀i∉E,w i≤ ell) :
    Finite.Optimal c w (eligibleRank E b c) :=
  tail_overload_rank_optimal E b w c ell hell hcard hb hmatch hw hout

end Rank

section PrivateMarks
variable {Ω : Type*} [Fintype Ω]

theorem private_any_upper_le (P : FiniteLaw Ω) {H : ℕ}
    (upper : Fin H→Ω→ Prop) (pi : ℝ)
    (hpi : ∀i,P.prob (upper i)≤ pi) :
    P.prob (fun w=>∃i,upper i w)≤(H:ℝ)*pi := by
  classical
  have hsum : P.prob (fun w=>∃i,upper i w)≤∑i : Fin H,P.prob (upper i) := by
    simp only [FiniteLaw.prob_eq_expect]
    rw [←FiniteLaw.expect_finset_sum]
    apply P.expect_mono
    intro w
    by_cases h:∃i,upper i w
    · obtain ⟨i,hi⟩ := h
      rw [if_pos ⟨i,hi⟩]
      have hh := Finset.single_le_sum
        (f:=fun k : Fin H=>if upper k w then (1:ℝ) else 0)
        (fun k _=>by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [if_pos hi] using hh
    · simp only [h,if_false]
      exact Finset.sum_nonneg (fun i _=>by split_ifs <;> norm_num)
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hpi i)
  calc
    _ ≤ ∑i : Fin H,P.prob (upper i) := hsum
    _ ≤ ∑_ : Fin H,pi := hh
    _ = (H:ℝ)*pi := by simp

theorem owner_acceptance_lower (P : FiniteLaw Ω) {H : ℕ}
    (upper : Fin H→Ω→ Prop) (accepted : Ω→ Prop) (pi : ℝ)
    (hpi : ∀i,P.prob (upper i)≤ pi)
    (homit : ∀w,¬accepted w→∃i,upper i w) :
    1-(H:ℝ)*pi≤ P.prob accepted := by
  have hu := private_any_upper_le P upper pi hpi
  have hc := P.prob_mono homit
  rw [P.prob_compl] at hc
  linarith

end PrivateMarks

end FCAppendix.Appendix08.Tail
