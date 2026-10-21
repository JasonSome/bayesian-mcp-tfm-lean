import FCAppendix.Existence.NarrowPayOnceGlobalReference
import FCAppendix.Existence.NarrowPayOnceUniformBand
import FCAppendix.Existence.NarrowPayOnceExpectedScore
import FCAppendix.PayOnce.PriceInteriorBounds

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology CommonList PayOnce PayOnce.OwnImpact Proposer
open scoped BigOperators

theorem success_abs_sub_le (n : ℕ) {p q : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) :
    |success n p-success n q|≤(n:ℝ)*|p-q| := by
  have hd (x : ℝ) (_hx : x∈Icc (0:ℝ) 1) :
      HasDerivWithinAt (success n) ((n:ℝ)*(1-x)^(n-1)) (Icc (0:ℝ) 1) x :=
    (hasDerivAt_success n x).hasDerivWithinAt
  have hb (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : ‖(n:ℝ)*(1-x)^(n-1)‖≤(n:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (by linarith [hx.2]) _))]
    have hh:(1-x)^(n-1)≤1 := pow_le_one₀ (by linarith [hx.2]) (by linarith [hx.1])
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ)≤n)]
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (convex_Icc (0:ℝ) 1) hq hp

section Threshold
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem rival_threshold_lower {n : ℕ} (hn : 2≤n) (b p : ι→ℝ) (L q low : ℝ)
    (hb : ∀i,0<b i) (hband : ∀i,low≤b i)
    (_hp : ∀i,p i∈Icc (0:ℝ) 1) (hq : q∈Ico (0:ℝ) 1)
    (hsum : ∑i,p i=(Fintype.card ι:ℝ)*q)
    (ht : ∀i,ScalarThreshold n (b i) L (p i)) : low*H n q≤L := by
  obtain ⟨i,hi⟩:=exists_coordinate_le_average p q hsum
  have hrec:=scalar_receipt_le_of_lt_one n (b i) L (p i) (ht i) (hi.trans_lt hq.2)
  have hH:=H_antitone n _ _ hi hq.2.le
  exact (mul_le_mul_of_nonneg_right (hband i)
    (H_pos n (by omega) q hq.1 hq.2.le).le).trans
    ((mul_le_mul_of_nonneg_left hH (hb i).le).trans hrec)

theorem rival_threshold_upper {n : ℕ} (hn : 2≤n) (b p : ι→ℝ) (L q high : ℝ)
    (hb : ∀i,0<b i) (hband : ∀i,b i≤high)
    (hp : ∀i,p i∈Icc (0:ℝ) 1) (hq : q∈Ioc (0:ℝ) 1)
    (hsum : ∑i,p i=(Fintype.card ι:ℝ)*q)
    (ht : ∀i,ScalarThreshold n (b i) L (p i)) : L≤high*H n q := by
  obtain ⟨i,hi⟩:=exists_coordinate_ge_average p q hsum
  have hrec:=scalar_price_le_of_pos n (b i) L (p i) (ht i) (hq.1.trans_le hi)
  have hH:=H_antitone n _ _ hi (hp i).2
  exact hrec.trans ((mul_le_mul_of_nonneg_left hH (hb i).le).trans
    (mul_le_mul_of_nonneg_right (hband i) (H_pos n (by omega) q hq.1.le hq.2).le))
end Threshold

section Row
variable {V : Type*} {n R c : ℕ} (hn : 2≤n) (hc : 1≤c) (hcR : c≤R)
    (beta : V→ℝ) {B θ : ℝ} (hθ : 0≤θ) (hB : θ<B)
    (hbeta : ∀v,|beta v-B|≤θ) (z : ℝ) (hz : 0<z) (omega : Fin R→V)

include hB hbeta hz in
private theorem row_positive (i : Fin (R+1)) : 0<rowBids beta z omega i := by
  refine Fin.cases hz (fun j=>?_) i
  change 0<beta (omega j)
  have hh:=(abs_le.mp (hbeta (omega j))).1
  linarith

include hn hc hcR hB hbeta hz in

theorem finiteRow_threshold :
    ∃L : ℝ,ScalarThreshold n z L (finiteRowMarginal n c beta z omega) ∧
      (0<finiteRowMarginal n c beta z omega →
        (B-θ)*H n (residual R c (finiteRowMarginal n c beta z omega))≤L) ∧
      (finiteRowMarginal n c beta z omega<1 →
        L≤(B+θ)*H n (residual R c (finiteRowMarginal n c beta z omega))) := by
  classical
  have hR : 0<R := by omega
  letI : Nonempty (Fin R):=⟨⟨0,hR⟩⟩
  let p:=kernelMarginal n c (rowBids beta z omega)
  have hp:=kernelMarginal_spec n hn c (rowBids beta z omega)
    (row_positive beta hB hbeta z hz omega)
  obtain ⟨L,_,ht⟩:=hp.2.2.2
  have hcard : c≤Fintype.card (Fin (R+1)) := by simp; omega
  have hsum : ∑j : Fin R,p j.succ=(R:ℝ)*residual R c (p 0) := by
    have he:=hp.2.2.1
    rw [Nat.min_eq_left hcard,Fin.sum_univ_succ] at he
    dsimp [residual]
    have hR0:(R:ℝ)≠0 := (Nat.cast_pos.mpr hR).ne'
    field_simp
    linarith
  have hq:=residual_bounds (Nat.cast_pos.mpr hR) (Nat.one_le_cast.mpr hc)
    (Nat.cast_le.mpr hcR) ⟨hp.1 0,hp.2.1 0⟩
  have hscalar (i : Fin (R+1)) : ScalarThreshold n (rowBids beta z omega i) L (p i) :=
    ⟨hp.1 i,hp.2.1 i,ht.1 i,ht.2.1 i,ht.2.2 i⟩
  refine ⟨L,by simpa only [rowBids,Fin.cons_zero,p,finiteRowMarginal] using hscalar 0,?_,?_⟩
  · intro hp0
    apply rival_threshold_lower hn (fun j : Fin R=>beta (omega j)) (fun j=>p j.succ)
      L (residual R c (p 0)) (B-θ)
    · intro j
      simpa only [rowBids,Fin.cons_succ] using row_positive beta hB hbeta z hz omega j.succ
    · intro j
      have hh:=(abs_le.mp (hbeta (omega j))).1
      linarith
    · intro j
      exact ⟨hp.1 _,hp.2.1 _⟩
    · refine ⟨hq.1,?_⟩
      apply (div_lt_one (Nat.cast_pos.mpr hR)).2
      have hh : (c:ℝ)≤R := Nat.cast_le.mpr hcR
      change 0<p 0 at hp0
      linarith
    · simpa only [Fintype.card_fin] using hsum
    · intro j
      simpa only [rowBids,Fin.cons_succ] using hscalar j.succ
  · intro hp1
    apply rival_threshold_upper hn (fun j : Fin R=>beta (omega j)) (fun j=>p j.succ)
      L (residual R c (p 0)) (B+θ)
    · intro j
      simpa only [rowBids,Fin.cons_succ] using row_positive beta hB hbeta z hz omega j.succ
    · intro j
      have hh:=(abs_le.mp (hbeta (omega j))).2
      linarith
    · intro j
      exact ⟨hp.1 _,hp.2.1 _⟩
    · refine ⟨?_,hq.2⟩
      apply div_pos _ (Nat.cast_pos.mpr hR)
      have hh : (1:ℝ)≤c := Nat.one_le_cast.mpr hc
      change p 0<1 at hp1
      linarith
    · simpa only [Fintype.card_fin] using hsum
    · intro j
      simpa only [rowBids,Fin.cons_succ] using hscalar j.succ

include hn hc hcR hθ hB hbeta hz in
theorem finiteRow_utility_le_reference (w w0 δ : ℝ) (hδ : 0≤δ) (hw : |w-w0|≤δ) :
    finiteRowUtility n c beta w z omega≤
      referenceUtility n R c w0 B (finiteRowMarginal n c beta z omega)+δ+(n:ℝ)*θ := by
  let p:=finiteRowMarginal n c beta z omega
  have hR : 0<R := by omega
  have hspec:=kernelMarginal_spec n hn c (rowBids beta z omega)
    (row_positive beta hB hbeta z hz omega)
  have hp:p∈Icc (0:ℝ) 1 := ⟨hspec.1 0,hspec.2.1 0⟩
  have hq:=residual_bounds (Nat.cast_pos.mpr hR) (Nat.one_le_cast.mpr hc)
    (Nat.cast_le.mpr hcR) hp
  have hH:=H_bounds n (by omega) (residual R c p) hq.1 hq.2
  have hS0:0 ≤ success n p := sub_nonneg.mpr (pow_le_one₀ (by linarith [hp.2]) (by linarith [hp.1]))
  have hS1:=success_le_one n p hp.2
  have htype:(w-w0)*success n p≤δ := by
    have ha:=(abs_le.mp hw).2
    nlinarith
  by_cases hp0:p=0
  · change (w-z)*success n p≤referenceUtility n R c w0 B p+δ+(n:ℝ)*θ
    simp only [hp0,success,sub_zero,one_pow,sub_self,mul_zero,referenceUtility,zero_mul,sub_zero]
    positivity
  have hpp:0<p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  obtain ⟨L,hown,hlo,_⟩:=finiteRow_threshold hn hc hcR beta hB hbeta z hz omega
  have hprice:= (hlo hpp).trans (scalar_price_le_of_pos n z L p hown hpp)
  have hpay:=mul_le_mul_of_nonneg_left hprice (mul_nonneg (Nat.cast_nonneg n) hp.1)
  have hunit:p*H n (residual R c p)≤1 := by
    simpa using mul_le_mul hp.2 hH.2
      (H_pos n (by omega) _ hq.1 hq.2).le (by norm_num : (0:ℝ)≤1)
  have herr:=mul_le_mul_of_nonneg_left hunit (mul_nonneg (Nat.cast_nonneg n) hθ)
  have hsid:=congrArg (fun x : ℝ=>z*x) (H_mul n (by omega) p)
  change (w-z)*success n p≤referenceUtility n R c w0 B p+δ+(n:ℝ)*θ
  dsimp [referenceUtility]
  nlinarith only [htype,hpay,herr,hsid]

include hn hc hcR hθ hB hbeta hz in

theorem finiteRow_bid_distance (hp : finiteRowMarginal n c beta z omega∈Ioo (0:ℝ) 1) :
    |z-B|≤(n:ℝ)*θ+2*B*(n:ℝ)^2*
      |finiteRowMarginal n c beta z omega-density R c| := by
  let p:=finiteRowMarginal n c beta z omega
  let q:=residual R c p
  let ρ:=density R c
  have hR : 0<R := by omega
  have hR1 : (1:ℝ)≤R := Nat.one_le_cast.mpr hR
  have hRpos : (0:ℝ)<R := Nat.cast_pos.mpr hR
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega : 0<n)
  have hBpos : 0<B := hθ.trans_lt hB
  have hq:q∈Icc (0:ℝ) 1 := residual_bounds hRpos (Nat.one_le_cast.mpr hc)
    (Nat.cast_le.mpr hcR) ⟨hp.1.le,hp.2.le⟩
  have hHp:=H_bounds n (by omega) p hp.1.le hp.2.le
  have hHq:=H_bounds n (by omega) q hq.1 hq.2
  obtain ⟨L,hown,hlo,hhi⟩:=finiteRow_threshold hn hc hcR beta hB hbeta z hz omega
  have hrec:z*H n p=L := hown.2.2.2.2 hp.1 hp.2
  have hprice:|L-B*H n q|≤θ := by
    have hl:=hlo hp.1
    have hh:=hhi hp.2
    have hθH:=mul_le_mul_of_nonneg_left hHq.2 hθ
    apply abs_le.mpr
    constructor <;> nlinarith
  have hqpeq:q-p=((R:ℝ)+1)/(R:ℝ)*(ρ-p) := by
    dsimp [q,ρ,residual,density]
    field_simp
    ring
  have hqp:|q-p|≤2*|p-ρ| := by
    rw [hqpeq,abs_mul,abs_of_nonneg (div_nonneg (by positivity) hRpos.le),abs_sub_comm ρ p]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply (div_le_iff₀ hRpos).2
    linarith
  have hHdiff:|H n q-H n p|≤2*(n:ℝ)*|p-ρ| :=
    (PayOnce.PriceInteriorBounds.H_abs_sub_le hn hq ⟨hp.1.le,hp.2.le⟩).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hqp hnpos.le])
  have hsplit:(z-B)*H n p=(L-B*H n q)+B*(H n q-H n p) := by nlinarith only [hrec]
  have habs:|z-B| * H n p≤θ+2*B*(n:ℝ)*|p-ρ| := by
    calc
      |z-B| * H n p=|(z-B)*H n p| := by rw [abs_mul,abs_of_pos (H_pos n (by omega) p hp.1.le hp.2.le)]
      _ = |(L-B*H n q)+B*(H n q-H n p)| := by rw [hsplit]
      _ ≤ |L-B*H n q|+|B*(H n q-H n p)| := abs_add_le _ _
      _ ≤ θ+B*(2*(n:ℝ)*|p-ρ|) := by
        rw [abs_mul,abs_of_pos hBpos]
        exact add_le_add hprice (mul_le_mul_of_nonneg_left hHdiff hBpos.le)
      _ = θ+2*B*(n:ℝ)*|p-ρ| := by ring
  have hbase:=mul_le_mul_of_nonneg_left hHp.1 (abs_nonneg (z-B))
  have htotal:=mul_le_mul_of_nonneg_right (hbase.trans habs) hnpos.le
  have hcancel:|z-B| * (1/(n:ℝ))*(n:ℝ)=|z-B| := by field_simp
  rw [hcancel] at htotal
  nlinarith only [htotal]

include hn hc hcR hθ hB hbeta in

theorem finiteRow_center_lower (w w0 δ : ℝ) (hδ : 0≤δ) (hw : |w-w0|≤δ)
    (hwB : B<w0) :
    (w0-B)*success n (density R c)-δ-
        (w0-B)*(n:ℝ)*(2*(n:ℝ)*θ/(B-θ))≤finiteRowUtility n c beta w B omega := by
  have hR : 0<R := by omega
  have hBpos : 0<B := hθ.trans_lt hB
  let p:=finiteRowMarginal n c beta B omega
  let ρ:=density R c
  have hrho:=density_bounds (Nat.cast_pos.mpr hR) (Nat.one_le_cast.mpr hc) (Nat.cast_le.mpr hcR)
  have hcap:(Fintype.card (Fin (R+1)):ℝ)*ρ=c := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    dsimp [ρ,density]
    field_simp
  have hband:∀i : Fin (R+1),|rowBids beta B omega i-B|≤θ := by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · simpa only [rowBids,Fin.cons_zero,sub_self,abs_zero] using hθ
    · simpa only [rowBids,Fin.cons_succ] using hbeta (omega j)
  have hpbound:=kernelMarginal_uniform_difference hn (by simp; omega : c≤Fintype.card (Fin (R+1)))
    hrho hθ hB hcap (rowBids beta B omega) hband 0
  have hspec:=kernelMarginal_spec n hn c (rowBids beta B omega)
    (row_positive beta hB hbeta B hBpos omega)
  have hp:p∈Icc (0:ℝ) 1 := ⟨hspec.1 0,hspec.2.1 0⟩
  have hs0:0 ≤ success n p := sub_nonneg.mpr (pow_le_one₀ (by linarith [hp.2]) (by linarith [hp.1]))
  have hs1:=success_le_one n p hp.2
  have hSdiff:= (success_abs_sub_le n hp ⟨hrho.1.le,hrho.2.le⟩).trans
    (mul_le_mul_of_nonneg_left hpbound (Nat.cast_nonneg n))
  have htype:(w0-w)*success n p≤δ := by
    have hh:=(abs_le.mp hw).1
    nlinarith
  have hpaydiff:=mul_le_mul_of_nonneg_left (abs_le.mp hSdiff).1 (sub_pos.mpr hwB).le
  change (w0-B)*success n ρ-δ-(w0-B)*(n:ℝ)*(2*(n:ℝ)*θ/(B-θ))≤(w-B)*success n p
  nlinarith only [htype,hpaydiff]

include hn hc hcR hθ hB hbeta hz in

theorem finiteRow_marginal_far (lo hi α eps : ℝ)
    (hrho : density R c∈Icc lo hi) (hαlo : α<lo) (hαhi : α<1-hi)
    (hsmall : (n:ℝ)*θ+2*B*(n:ℝ)^2*α<eps) (hfar : eps≤|z-B|) :
    α < |finiteRowMarginal n c beta z omega-density R c| := by
  by_contra hh
  have hdist:=abs_le.mp (le_of_not_gt hh)
  have hp:finiteRowMarginal n c beta z omega∈Ioo (0:ℝ) 1 := by
    constructor <;> linarith [hrho.1,hrho.2]
  have hbid:=finiteRow_bid_distance hn hc hcR beta hθ hB hbeta z hz omega hp
  have hBpos:0<B := hθ.trans_lt hB
  have hmul:=mul_le_mul_of_nonneg_left (le_of_not_gt hh)
    (show (0:ℝ)≤2*B*(n:ℝ)^2 by positivity)
  linarith

end Row
end FCAppendix.Existence.NarrowPayOnce
