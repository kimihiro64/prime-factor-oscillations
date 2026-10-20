/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.BernoulliProfileReconstruction

/-!
# Fixed shifts between ordered probability tails

Equal positive-value sets determine eventually strictly decreasing positive
sequences tending to zero up to a fixed tail shift. Finite exceptional values
are excluded explicitly before comparing the two ordered tails.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

private theorem strictAnti_eq_of_mutual_values {R : Type*} [Preorder R]
    (f g : Nat -> R) (hf : StrictAnti f) (hg : StrictAnti g)
    (hfg : forall n, exists m, g m = f n)
    (hgf : forall n, exists m, f m = g n) : f = g := by
  let t : Nat -> Nat := fun n => Classical.choose (hfg n)
  let u : Nat -> Nat := fun n => Classical.choose (hgf n)
  have ht : forall n, g (t n) = f n := fun n => Classical.choose_spec (hfg n)
  have hu : forall n, f (u n) = g n := fun n => Classical.choose_spec (hgf n)
  have htm : StrictMono t := by
    intro i j hij
    apply hg.lt_iff_gt.mp
    rw [ht, ht]
    exact hf hij
  have hum : StrictMono u := by
    intro i j hij
    apply hf.lt_iff_gt.mp
    rw [hu, hu]
    exact hg hij
  have hcomp : forall n, u (t n) = n := by
    intro n
    apply hf.injective
    rw [hu, ht]
  have hid : forall n, t n = n := by
    intro n
    apply le_antisymm ?_ (htm.id_le n)
    calc
      t n <= u (t n) := hum.id_le (t n)
      _ = n := hcomp n
  funext n
  rw [<- ht n, hid n]

private theorem tail_index_ge_of_value_le
    (f : Nat -> Real) (c : Real) (M A : Nat) (hMA : M <= A)
    (hf : StrictAnti (fun n => f (M + n)))
    (hsmall : forall j : Fin M, 0 < f j.val -> c < f j.val)
    (hA : f A = c) {j : Nat} (hjpos : 0 < f j) (hjle : f j <= c) : A <= j := by
  have hMj : M <= j := by
    by_contra hn
    exact (not_lt_of_ge hjle) (hsmall (Fin.mk j (Nat.lt_of_not_ge hn)) hjpos)
  have hle : A - M <= j - M := hf.le_iff_ge.mp (by
    simpa only [Nat.add_sub_of_le hMj, Nat.add_sub_of_le hMA, hA] using hjle)
  omega

private theorem tail_value_cover
    (f g : Nat -> Real) (c : Real) (A M B : Nat)
    (hMB : M <= B) (hfA : f A = c) (hgB : g B = c)
    (hfpos : forall n, 0 < f (A + n))
    (hf : StrictAnti (fun n => f (A + n)))
    (hg : StrictAnti (fun n => g (M + n)))
    (hsmall : forall j : Fin M, 0 < g j.val -> c < g j.val)
    (hvalues : forall n, 0 < f n -> exists j, g j = f n) :
    forall n, exists m, g (B + m) = f (A + n) := by
  intro n
  let j := Classical.choose (hvalues (A + n) (hfpos n))
  have hj : g j = f (A + n) := Classical.choose_spec (hvalues (A + n) (hfpos n))
  have hjpos : 0 < g j := by rw [hj]; exact hfpos n
  have hjle : g j <= c := by
    rw [hj]
    simpa only [Nat.add_zero, hfA] using hf.antitone (Nat.zero_le n)
  have hjB := tail_index_ge_of_value_le g c M B hMB hg hsmall hgB hjpos hjle
  refine Exists.intro (j - B) ?_
  simpa only [Nat.add_sub_of_le hjB] using hj

/-- Positive-value equality fixes ordered tails after one constant index shift. -/
theorem exists_tail_shift_of_positive_values
    (a b : Nat -> Real) (Ma Mb : Nat)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hapos : forall n, Ma <= n -> 0 < a n)
    (hbpos : forall n, Mb <= n -> 0 < b n)
    (ha : StrictAnti (fun n => a (Ma + n)))
    (hb : StrictAnti (fun n => b (Mb + n)))
    (hvalues : forall c : Real, 0 < c ->
      ((exists n, a n = c) <-> exists n, b n = c)) :
    exists A B, Ma <= A /\ Mb <= B /\ forall n, a (A + n) = b (B + n) := by
  have hsmalla : Filter.Eventually
      (fun n => forall j : Fin Ma, 0 < a j.val -> a n < a j.val) Filter.atTop := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : 0 < a j.val
    . exact (ha0.eventually (gt_mem_nhds hj)).mono (fun _ hn _ => hn)
    . exact Filter.Eventually.of_forall (fun _ hp => False.elim (hj hp))
  have hsmallb : Filter.Eventually
      (fun n => forall j : Fin Mb, 0 < b j.val -> a n < b j.val) Filter.atTop := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : 0 < b j.val
    . exact (ha0.eventually (gt_mem_nhds hj)).mono (fun _ hn _ => hn)
    . exact Filter.Eventually.of_forall (fun _ hp => False.elim (hj hp))
  have hex := Filter.eventually_atTop.mp (hsmalla.and hsmallb)
  let N := Classical.choose hex
  let A := max Ma N
  have hA : Ma <= A := le_max_left _ _
  have hsmall := Classical.choose_spec hex A (le_max_right _ _)
  have hApos : 0 < a A := hapos A hA
  have hmatch := (hvalues (a A) hApos).mp (Exists.intro A rfl)
  let B := Classical.choose hmatch
  have hBval : b B = a A := Classical.choose_spec hmatch
  have hBpos : 0 < b B := by rw [hBval]; exact hApos
  have hB : Mb <= B := by
    by_contra hn
    have hbad := hsmall.2 (Fin.mk B (Nat.lt_of_not_ge hn)) hBpos
    rw [hBval] at hbad
    exact lt_irrefl _ hbad
  have haTail : StrictAnti (fun n => a (A + n)) := by
    intro i j hij
    simpa only [<- Nat.add_assoc, Nat.add_sub_of_le hA] using
      ha (Nat.add_lt_add_left hij (A - Ma))
  have hbTail : StrictAnti (fun n => b (B + n)) := by
    intro i j hij
    simpa only [<- Nat.add_assoc, Nat.add_sub_of_le hB] using
      hb (Nat.add_lt_add_left hij (B - Mb))
  have haposTail : forall n, 0 < a (A + n) := by
    intro n
    apply hapos
    omega
  have hbposTail : forall n, 0 < b (B + n) := by
    intro n
    apply hbpos
    omega
  have hab : forall n, exists m, b (B + m) = a (A + n) :=
    tail_value_cover a b (a A) A Mb B hB rfl hBval haposTail haTail hb hsmall.2
      (fun n hn => (hvalues (a n) hn).mp (Exists.intro n rfl))
  have hba : forall n, exists m, a (A + m) = b (B + n) :=
    tail_value_cover b a (a A) B Ma A hA hBval rfl hbposTail hbTail ha hsmall.1
      (fun n hn => (hvalues (b n) hn).mpr (Exists.intro n rfl))
  refine Exists.intro A (Exists.intro B (And.intro hA (And.intro hB ?_)))
  exact congrFun (strictAnti_eq_of_mutual_values _ _ haTail hbTail hab hba)

/-- Equal profiles align eventually strictly ordered positive probability tails. -/
theorem exists_tail_shift_of_canonicalBernoulliProfile_eq
    (a b : Nat -> Real) (Ma Mb : Nat)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hb : forall n, 0 <= b n) (hb1 : forall n, b n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2)) (hsb : Summable (fun n => (b n) ^ 2))
    (hprofile : canonicalBernoulliProfile a = canonicalBernoulliProfile b)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hapos : forall n, Ma <= n -> 0 < a n)
    (hbpos : forall n, Mb <= n -> 0 < b n)
    (haanti : StrictAnti (fun n => a (Ma + n)))
    (hbanti : StrictAnti (fun n => b (Mb + n))) :
    exists A B, Ma <= A /\ Mb <= B /\ forall n, a (A + n) = b (B + n) := by
  have hmatch := exists_positive_equiv_of_canonicalBernoulliProfile_eq
    a b ha ha1 hb hb1 hsa hsb hprofile
  let e := Classical.choose hmatch
  have he := Classical.choose_spec hmatch
  change forall i : {n : Nat // 0 < a n}, a i.val = b (e i).val at he
  have hvalues : forall c : Real, 0 < c ->
      ((exists n, a n = c) <-> exists n, b n = c) := by
    intro c hc
    constructor
    . intro h
      let n := Classical.choose h
      have hn : a n = c := Classical.choose_spec h
      have hp : 0 < a n := by rw [hn]; exact hc
      let i : {n : Nat // 0 < a n} := Subtype.mk n hp
      exact Exists.intro (e i).val ((he i).symm.trans hn)
    . intro h
      let n := Classical.choose h
      have hn : b n = c := Classical.choose_spec h
      have hp : 0 < b n := by rw [hn]; exact hc
      let j : {n : Nat // 0 < b n} := Subtype.mk n hp
      have heq : a (e.symm j).val = b n := by
        simpa only [Equiv.apply_symm_apply] using he (e.symm j)
      exact Exists.intro (e.symm j).val (heq.trans hn)
  exact exists_tail_shift_of_positive_values a b Ma Mb ha0 hapos hbpos
    haanti hbanti hvalues

end Complex
