/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCorrelationPoisson

/-!
# IntegerQuadraticFourModulus

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-! Admissibility of the exact modulus in every off-diagonal packet row. -/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticFourModulus

open IntegerQuadraticInitial

theorem larger_prime_coprime (a p : Nat) (ha : 0 < a) (hap : a < p)
    (hp : Nat.Prime p) : Nat.Coprime a p := by
  rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right a p) with h | h
  . exact h
  . have hd : Dvd.dvd p a := by
      rw [<- h]
      exact Nat.gcd_dvd_left a p
    have hl := Nat.le_of_dvd ha hd
    omega

theorem four_modulus_good (a b r s : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (haodd : Odd a) (hbodd : Odd b) (hrodd : Odd r) (hsodd : Odd s)
    (hasf : Squarefree a) (hbsf : Squarefree b) (hab : Nat.Coprime a b)
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs : Not (r = s))
    (har : a < r) (has : a < s) (hbr : b < r) (hbs : b < s) :
    Good ((a * b) * (r * s)) := by
  have hcp_ar := larger_prime_coprime a r ha har hr
  have hcp_as := larger_prime_coprime a s ha has hs
  have hcp_br := larger_prime_coprime b r hb hbr hr
  have hcp_bs := larger_prime_coprime b s hb hbs hs
  have hcp_rs : Nat.Coprime r s := by
    by_cases hlt : r < s
    . exact larger_prime_coprime r s hr.pos hlt hs
    . have hlt' : s < r := by omega
      exact (larger_prime_coprime s r hs.pos hlt' hr).symm
  have hcp_all : Nat.Coprime (a * b) (r * s) :=
    (hcp_ar.mul_right hcp_as).mul_left (hcp_br.mul_right hcp_bs)
  have hsf_ab : Squarefree (a * b) :=
    Nat.squarefree_mul_iff.mpr (And.intro hab (And.intro hasf hbsf))
  have hsf_rs : Squarefree (r * s) :=
    Nat.squarefree_mul_iff.mpr (And.intro hcp_rs (And.intro hr.squarefree hs.squarefree))
  have hsf : Squarefree ((a * b) * (r * s)) :=
    Nat.squarefree_mul_iff.mpr (And.intro hcp_all (And.intro hsf_ab hsf_rs))
  have hodd : Odd ((a * b) * (r * s)) :=
    Nat.odd_mul.mpr (And.intro (Nat.odd_mul.mpr (And.intro haodd hbodd))
      (Nat.odd_mul.mpr (And.intro hrodd hsodd)))
  have habpos : 1 <= a * b := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
    (Nat.ne_of_gt ha) (Nat.ne_of_gt hb))
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have hrs4 : 4 <= r * s := by nlinarith
  have hle : r * s <= (a * b) * (r * s) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (r * s) habpos
  have hgt : 1 < (a * b) * (r * s) := by omega
  exact And.intro hgt (And.intro hodd hsf)

theorem packet_modulus_good (n1 n2 r s : Nat)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (ho1 : Odd n1) (ho2 : Odd n2)
    (hf1 : Squarefree n1) (hf2 : Squarefree n2)
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hro : Odd r) (hso : Odd s)
    (hrs : Not (r = s))
    (h1r : n1 < r) (h1s : n1 < s) (h2r : n2 < r) (h2s : n2 < s) :
    Good (((n1 / Nat.gcd n1 n2) * (n2 / Nat.gcd n1 n2)) * (r * s)) := by
  let g := Nat.gcd n1 n2
  let a := n1 / g
  let b := n2 / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right n1 hn2
  have h1 : g * a = n1 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left n1 n2)
  have h2 : g * b = n2 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right n1 n2)
  have hfa : Squarefree a := (Nat.squarefree_mul_iff.mp
    (show Squarefree (g * a) by rw [h1]; exact hf1)).2.2
  have hfb : Squarefree b := (Nat.squarefree_mul_iff.mp
    (show Squarefree (g * b) by rw [h2]; exact hf2)).2.2
  have hoa : Odd a := (Nat.odd_mul.mp
    (show Odd (g * a) by rw [h1]; exact ho1)).2
  have hob : Odd b := (Nat.odd_mul.mp
    (show Odd (g * b) by rw [h2]; exact ho2)).2
  have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => by
    have hz1 : n1 = 0 := by rw [<- h1, hz, Nat.mul_zero]
    exact (Nat.ne_of_gt hn1) hz1)
  have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => by
    have hz2 : n2 = 0 := by rw [<- h2, hz, Nat.mul_zero]
    exact (Nat.ne_of_gt hn2) hz2)
  have hab : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg
  have har : a < r := lt_of_le_of_lt (Nat.div_le_self n1 g) h1r
  have has : a < s := lt_of_le_of_lt (Nat.div_le_self n1 g) h1s
  have hbr : b < r := lt_of_le_of_lt (Nat.div_le_self n2 g) h2r
  have hbs : b < s := lt_of_le_of_lt (Nat.div_le_self n2 g) h2s
  exact four_modulus_good a b r s ha hb hoa hob hro hso hfa hfb hab
    hr hs hrs har has hbr hbs

end PrimeFactorOscillations.IntegerQuadraticFourModulus

