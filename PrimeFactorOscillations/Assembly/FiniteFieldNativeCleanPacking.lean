/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import PrimeFactorOscillations.Assembly.FiniteFieldNativeRowFibres

/-!
# Finite native packings after a square-factor cutoff

A short prime-pair collection with bounded square divisors in its gaps has
a large subcollection whose distinct native agreement rates are three eighths.
The proof keeps both squareclass rows and counts their shared endpoint fibres.
This finite theorem is the combinatorial consumer for height-capacity bounds;
it does not itself estimate how many pairs survive the cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_clean_gap_packing (S : Finset (Prod Nat Nat)) (T : Nat)
    (hprime : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.2 < a.1)
    (hclean : forall a : Prod Nat Nat, Membership.mem S a ->
      forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2)) :
    exists M : Finset (Prod Nat Nat),
      (forall a : Prod Nat Nat, Membership.mem M a -> Membership.mem S a) /\
      S.card <= 2 * (T - 1) * M.card /\
      forall a : Prod Nat Nat, Membership.mem M a ->
        forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  classical
  have hfactor : forall a : Prod Nat Nat, exists d u : Nat,
      Membership.mem S a ->
        0 < d /\ 0 < u /\ u ^ 2 * d = a.2 /\ Squarefree d := by
    intro a
    by_cases ha : Membership.mem S a
    . choose d u hd hu he hs using Nat.sq_mul_squarefree_of_pos (hprime a ha).2.2.1
      exact Exists.intro d (Exists.intro u (fun _ => And.intro hd
        (And.intro hu (And.intro he hs))))
    . exact Exists.intro 1 (Exists.intro 1 (fun h => False.elim (ha h)))
  choose d u hdu using hfactor
  have hroot (a : Prod Nat Nat) (ha : Membership.mem S a) : u a < T := by
    by_contra hnot
    exact hclean a ha (u a) (le_of_not_gt hnot)
      (Exists.intro (d a) (hdu a ha).2.2.1.symm)
  let L : Prod Nat Nat -> Prod Nat Nat := fun a => Prod.mk a.1 (d a)
  let U : Prod Nat Nat -> Prod Nat Nat := fun a => Prod.mk (a.1 + a.2) (d a)
  have hL (x : Prod Nat Nat) :
      (S.filter (fun a => L a = L x)).card <= T - 1 := by
    have hc : (S.filter (fun a => L a = L x)).card <= (Finset.Ico 1 T).card := by
      apply Finset.card_le_card_of_injOn u
      . intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        exact Finset.mem_Ico.mpr (And.intro (hdu a haS).2.1 (hroot a haS))
      . intro a ha b hb he
        have haS := (Finset.mem_filter.mp ha).1
        have hbS := (Finset.mem_filter.mp hb).1
        have hl : L a = L b :=
          (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        have hn : a.1 = b.1 := by
          have hp := congrArg (fun z : Prod Nat Nat => z.1) hl
          exact hp
        have hd : d a = d b := congrArg Prod.snd hl
        have hh : a.2 = b.2 := by
          rw [<- (hdu a haS).2.2.1, <- (hdu b hbS).2.2.1, he, hd]
        exact Prod.ext hn hh
    simpa using hc
  have hU (x : Prod Nat Nat) :
      (S.filter (fun a => U a = U x)).card <= T - 1 := by
    have hc : (S.filter (fun a => U a = U x)).card <= (Finset.Ico 1 T).card := by
      apply Finset.card_le_card_of_injOn u
      . intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        exact Finset.mem_Ico.mpr (And.intro (hdu a haS).2.1 (hroot a haS))
      . intro a ha b hb he
        have haS := (Finset.mem_filter.mp ha).1
        have hbS := (Finset.mem_filter.mp hb).1
        have hl : U a = U b :=
          (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        have hn : a.1 + a.2 = b.1 + b.2 := congrArg Prod.fst hl
        have hd : d a = d b := congrArg Prod.snd hl
        have hh : a.2 = b.2 := by
          rw [<- (hdu a haS).2.2.1, <- (hdu b hbS).2.2.1, he, hd]
        exact Prod.ext (by omega) hh
    simpa using hc
  have hcore (a b : Prod Nat Nat) (ha : Membership.mem S a)
      (hb : Membership.mem S b) (v : Nat) (hv : 0 < v)
      (hs : IsSquare (a.2 * b.2 * v * v)) : d a = d b := by
    let z := Classical.choose hs
    have hz : a.2 * b.2 * v * v = z * z := Classical.choose_spec hs
    let w := u a * u b * v
    have hw : 0 < w := Nat.mul_pos
      (Nat.mul_pos (hdu a ha).2.1 (hdu b hb).2.1) hv
    have he : w * w * (d a * d b) = z * z := by
      calc
        w * w * (d a * d b) = a.2 * b.2 * v * v := by
          rw [<- (hdu a ha).2.2.1, <- (hdu b hb).2.2.1]
          dsimp [w]
          ring
        _ = z * z := hz
    have hdiv : Dvd.dvd (w ^ 2) (z ^ 2) :=
      Exists.intro (d a * d b) (by simpa only [pow_two] using he.symm)
    have hdz : Dvd.dvd w z :=
      (Nat.pow_dvd_pow_iff (by decide : Not ((2 : Nat) = 0))).mp hdiv
    let t := Classical.choose hdz
    have hzt : z = w * t := Classical.choose_spec hdz
    have he' : (w * w) * (d a * d b) = (w * w) * (t * t) := by
      calc
        (w * w) * (d a * d b) = z * z := he
        _ = (w * w) * (t * t) := by rw [hzt]; ring
    have hsq : IsSquare (d a * d b) :=
      Exists.intro t (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hw hw) he')
    have hsq' : IsSquare (d b * d a) := by simpa only [mul_comm] using hsq
    exact Nat.dvd_antisymm
      (Squarefree.dvd_of_isSquare_mul (hdu a ha).2.2.2 hsq)
      (Squarefree.dvd_of_isSquare_mul (hdu b hb).2.2.2 hsq')
  let good : Finset (Prod Nat Nat) -> Prop := fun V =>
    forall a : Prod Nat Nat, Membership.mem V a ->
      forall b : Prod Nat Nat, Membership.mem V b -> Not (a = b) ->
        Not (L a = L b) /\ Not (U a = U b)
  let C := S.powerset.filter good
  have hempty : Membership.mem C (Finset.empty : Finset (Prod Nat Nat)) := by
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_powerset.mpr (Finset.empty_subset S)) ?_
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  choose M hMC hmax using Finset.exists_max_image C Finset.card
    (Exists.intro Finset.empty hempty)
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hMC).1
  have hgood : good M := (Finset.mem_filter.mp hMC).2
  have hcover : forall a : Prod Nat Nat, Membership.mem S a ->
      exists b : Prod Nat Nat, Membership.mem M b /\ (L a = L b \/ U a = U b) := by
    intro a ha
    by_contra hnone
    have haM : Not (Membership.mem M a) := by
      intro h
      exact hnone (Exists.intro a (And.intro h (Or.inl rfl)))
    have hInsGood : good (insert a M) := by
      intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with hba | hbM
      . subst b
        rcases Finset.mem_insert.mp hc with hca | hcM
        . subst c
          exact False.elim (hbc rfl)
        . constructor
          . intro h
            exact hnone (Exists.intro c (And.intro hcM (Or.inl h)))
          . intro h
            exact hnone (Exists.intro c (And.intro hcM (Or.inr h)))
      . rcases Finset.mem_insert.mp hc with hca | hcM
        . subst c
          constructor
          . intro h
            exact hnone (Exists.intro b (And.intro hbM (Or.inl h.symm)))
          . intro h
            exact hnone (Exists.intro b (And.intro hbM (Or.inr h.symm)))
        . exact hgood b hbM c hcM hbc
    have hInsSub : forall b : Prod Nat Nat,
        Membership.mem (insert a M) b -> Membership.mem S b := by
      intro b hb
      rcases Finset.mem_insert.mp hb with hba | hbM
      . rw [hba]
        exact ha
      . exact hsub hbM
    have hInsMem : Membership.mem C (insert a M) :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_powerset.mpr hInsSub) hInsGood)
    have hbad := hmax (insert a M) hInsMem
    rw [Finset.card_insert_of_notMem haM] at hbad
    omega
  let N : Prod Nat Nat -> Finset (Prod Nat Nat) := fun b =>
    Union.union (S.filter (fun a => L a = L b)) (S.filter (fun a => U a = U b))
  have hNb (b : Prod Nat Nat) : (N b).card <= (T - 1) + (T - 1) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hL b) (hU b))
  have hcount : S.card <= 2 * (T - 1) * M.card := by
    have hcoverSub : forall a : Prod Nat Nat,
        Membership.mem S a -> Membership.mem (M.biUnion N) a := by
      intro a ha
      choose b hb hrow using hcover a ha
      apply Finset.mem_biUnion.mpr
      refine Exists.intro b (And.intro hb ?_)
      change Membership.mem
        (Union.union (S.filter (fun c => L c = L b)) (S.filter (fun c => U c = U b))) a
      rcases hrow with hl | hu
      . exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr (And.intro ha hl)))
      . exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr (And.intro ha hu)))
    calc
      S.card <= (M.biUnion N).card := Finset.card_le_card hcoverSub
      _ <= Finset.sum M (fun b => (N b).card) := Finset.card_biUnion_le
      _ <= Finset.sum M (fun _ => 2 * (T - 1)) := by
        apply Finset.sum_le_sum
        intro b hb
        simpa only [two_mul] using hNb b
      _ = M.card * (2 * (T - 1)) := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * (T - 1) * M.card := Nat.mul_comm _ _
  refine Exists.intro M (And.intro hsub (And.intro hcount ?_))
  intro a ha b hb hneq
  have haS := hsub ha
  have hbS := hsub hb
  have haP := hprime a haS
  have hbP := hprime b hbS
  have hneq' : Not (And (a.1 = b.1) (a.2 = b.2)) := by
    intro h
    exact hneq (Prod.ext h.1 h.2)
  apply (native_agreement_arithmetic_classification a.1 a.2 b.1 b.2
    haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1 hneq').2.mpr
  have hsep := hgood a ha b hb hneq
  constructor
  . intro hs
    have hn : a.1 = b.1 :=
      (native_square_rows_recover_endpoints a.1 a.2 b.1 b.2
        haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1).1
          haP.2.2.2 hbP.2.2.2 hs
    have hs' : IsSquare (a.2 * b.2 * a.1 * a.1) := by
      simpa only [<- hn] using hs
    have hd := hcore a b haS hbS a.1 haP.1.pos hs'
    exact hsep.1 (Prod.ext hn hd)
  . intro hs
    have hq : a.1 + a.2 = b.1 + b.2 :=
      (native_square_rows_recover_endpoints a.1 a.2 b.1 b.2
        haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1).2 hs
    have hs' : IsSquare (a.2 * b.2 * (a.1 + a.2) * (a.1 + a.2)) := by
      simpa only [<- hq] using hs
    have hd := hcore a b haS hbS (a.1 + a.2) haP.2.1.pos hs'
    exact hsep.2 (Prod.ext hq hd)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
